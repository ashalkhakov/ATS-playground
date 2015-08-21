// static arrray with shared pointers taken out from it
#include
"share/atspre_staload.hats"

staload _ = "prelude/DATS/integer.dats"
staload _ = "prelude/DATS/pointer.dats"

(* ****** ****** *)
//
// HX: subview relation that only allows *reading*
//
absprop vsubr_p (v1:view+, v2: view-) // v2 -<prf> [v:iew] @(v1, v)
stadef <= (v1:view, v2:view) = vsubr_p (v1, v2)
//
// HX: subview relation that allows *reading* and *writing*
//
absprop vsubw_p (v1:view, v2: view) // v2 -<prf> @(v1, v1 -<lin,prf> v2)
//

extern
prfun vsubr_intr {v1,v2:view}
(fpf: v2 -<prf> [v:view] (v1, v)): vsubr_p (v1, v2)
// implemented in [vsubrw.dats]
extern
prfun vsubr_elim {v1,v2:view}
(pf: vsubr_p (v1, v2)):<> v2 -<prf> [v:view] (v1, v)
// implemented in [vsubrw.dats]
extern
prfun vsubr_refl {v:view} (): vsubr_p (v, v)
extern
prfun vsubr_trans {v1,v2,v3:view}
(pf12: vsubr_p (v1, v2), pf23: vsubr_p (v2, v3)): vsubr_p (v1, v3)
// end of [vcontain_trans]
extern
prfun vsubr_of_vsubw {v1,v2:view} (pf: vsubw_p (v1, v2)): vsubr_p (v1, v2)
extern
prfun vsubr_tup_2_0 {v0,v1:view} (): vsubr_p (v0, @(v0, v1))
extern
prfun vsubr_tup_2_1 {v0,v1:view} (): vsubr_p (v1, @(v0, v1))
(* ****** ****** *)
extern
prfun vsubw_intr {v1,v2:view}
(fpf: v2 -<prf> (v1, v1 -<lin,prf> v2)): vsubw_p (v1, v2)
// implemented in [vsubrw.dats]
extern
prfun vsubw_elim {v1,v2:view}
(pf: vsubw_p (v1, v2)):<> v2 -<prf> (v1, v1 -<lin,prf> v2)
// implemented in [vsubrw.dats]
extern
prfun vsubw_tup_2_0 {v0,v1:view} (): vsubw_p (v0, @(v0, v1))
extern
prfun vsubw_tup_2_1 {v0,v1:view} (): vsubw_p (v1, @(v0, v1))
(* ****** ****** *)
extern
prval vsubw_array_elt :
{a:viewt@ype} {n,i:nat | i < n} {l:addr}
() -<> vsubw_p (a @ l + i*sizeof(a), @[a][n] @ l)
extern
prval vsubw_array_subarray :
{a:viewt@ype} {n0,i,n:nat | i+n <= n0} {l:addr}
() -<> vsubw_p (@[a][n] @ l + i*sizeof(a), @[a][n0] @ l)

(* ****** ****** *)

// is this sound?
absview stamped_v (v:view, int) // = v
extern
prval stamped_intr : {v:view} v -<> [s:int] stamped_v (v, s)
extern
prval stamped_elim : {v:view} {s:int} stamped_v (v, s) -<> v
// NOTE: I guess this is sound because [v] isn't really changeable?
extern
prval vsubw_stamped_unstamped :
{v:view} {s:int}
() -<> vsubw_p (v, stamped_v (v, s))

dataprop EQVIEW (view, view) = {a:view} EQVIEW (a, a)

extern
prval stamped_eq :
{v1,v2:view} {s:int}
(!stamped_v (v1, s), !stamped_v (v2, s)) -<> EQVIEW (v1, v2)

(* ****** ****** *)

#define TP int

abstype aref = ptr
absview aview
extern
fun
aref_read (!aview | aref): TP
extern
fun
aref_write (!aview | aref, TP): void
extern
fun
aref_make (!aview | i: int): aref
extern
castfn
aview_get ():<!ref> (aview, aview -<lin,prf> void | void)

local

#define NUMELT 5

var p_arr1 = @[TP][NUMELT](1,2,3,4,5)
val p_arr = addr@(p_arr1)
prval pf_arr = view@(p_arr1)
prval [l_arr:addr] EQADDR () = eqaddr_make_ptr (p_arr)

// indexed: aref (a:t@ype, l_base:addr, n:int)
// - too much indexing... replace l_base, n with a single "stamp"
// - see stamping above
// - next, use aref (int(*stamp*))
// - aref (s:int) = [a:t@ype;l:addr;v:view] (vsubw_p (a @ l, stamped_v (v, s)) | ptr l)
//   - you can prove that the [v] in the ref is same as another view by
//     invoking [eq] (since stamps are the same)
//   - knowing what [v] is equivalent to, you can use the [vsubw] proof to obtain the at-proof
// WHAT ABOUT a simpler scheme!
//   aref (a:t@ype, v:view) = [l:addr] (vsubw_p (a @ l, v) | ptr l)
// - we don't mention what the view must be...
assume aref = [l:addr] (vsubw_p (TP @ l, @[TP][NUMELT] @ l_arr) | ptr l)
assume aview = @[TP][NUMELT] @ l_arr

in // in of [local]

implement
aref_read (pf_arr | x) = let
  prval fpf0 = vsubw_elim (x.0)
  prval (pf_at, fpf1) = fpf0 (pf_arr)
  val res = ptr_get<TP> (pf_at | x.1)
  prval () = pf_arr := fpf1 (pf_at)
in
  res
end

implement
aref_write (pf_arr | x, v) = let
  prval fpf0 = vsubw_elim (x.0)
  prval (pf_at, fpf1) = fpf0 (pf_arr)
  val () = ptr_set<TP> (pf_at | x.1, v)
  prval () = pf_arr := fpf1 (pf_at)
in
  // nothing
end

implement
aref_make (pf_arr | i) = let
  val i = g1ofg0 (i)
  prval [i:int] EQINT () = eqint_make_gint (i)
  val () = assert_errmsg (i >= 0, "aref_make: out of bounds!")
  val () = assert_errmsg (i < NUMELT, "aref_make: out of bounds!")
  prval pf = vsubw_array_elt {TP} {NUMELT,i} {l_arr} ()
  val p = ptr1_add_gint<TP> (p_arr, i)
  prval [l1:addr] EQADDR () = eqaddr_make_ptr (p)
in
  #[l1 | (pf | p)]
end

end // end of [local]

fun
do_stuff (): void = let
  val () = println!("do stuff: start")
  prval (pf_arr, fpf | ()) = $effmask_ref (aview_get ())
  val ref1 = aref_make (pf_arr | 1)
  val ref2 = aref_make (pf_arr | 2)
  val ref3 = aref_make (pf_arr | 3)
  val () = println!("[1] = ", aref_read (pf_arr | ref1), ", [2] = ", aref_read (pf_arr | ref2))
  val () = aref_write (pf_arr | ref2, 5)
  val () = println!("[2] = ", aref_read (pf_arr | ref2))
  prval () = fpf (pf_arr)
  val () = println!("do stuff: completed")
in
end // end of [do_stuff]

(* ****** ****** *)

// another attempt
// - pool of objects (stapool)
// - pool memory is allocated by the user
// - pointers into the pool are easily shared (so, as many takeouts
//   as one wants)
// - reading from/writing to addresses still requires
//   a linear permission

(* ****** ****** *)
//
absvt@ype stapool_vt (a:t@ype, int, int, addr) = @(ptr, size_t, ptr)
vtypedef stapool_vt0 (a:t@ype) = stapool_vt (a, 0, 0, null)?
vtypedef stapool_vt1 (a:t@ype, n:int, l:addr) = [i:int | i <= n] stapool_vt (a, i, n, l)
//
abstype pptr (a:t@ype, addr) = ptr
//
extern
fun{a:t@ype}
stapool_init {n:int} {l:addr} (
  array_v (a?, l, n)
| ptr l
, size_t n
, &stapool_vt0 (a) >> stapool_vt (a, 0, n, l)
): void
//
extern
prfun
stapool_free {a:t@ype} {n,m:int} {l:addr} (
  // NB. the type given to buf after returning
  // is the same as what it was prior to [stapool_init]
  !stapool_vt (a, n, m, l) >> stapool_vt0 (a)
): array_v (a?, l, m)
extern
fun{a:t@ype}
stapool_is_full {n,m:int} {l:addr} (
  &stapool_vt (a, n, m, l) >> _
): bool (n < m)
//
extern
fun{a:t@ype}
stapool_alloc {n,m:int | n < m} {l:addr} (
  &stapool_vt (a, n, m, l) >> stapool_vt (a, n+1, m, l)
, a
): pptr (a, l)
//
extern
fun{a:t@ype}
pptr_read {n,m:int} {l:addr} (&stapool_vt (a, n, m, l), pptr (a, l)): a
//
extern
fun{a:t@ype}
pptr_write {n,m:int} {l:addr} (&stapool_vt (a, n, m, l), pptr (a, l), a): void
//
(* ****** end of [stapool.sats] ****** *)

//
local
//
// NB. the structure of the type closely follows
// the structure given in the interface; we are only
// allowed to refine the tuple elements, but not
// add some new elements, even if we only add proofs
// NB. we don't add a top-level constraint to the top (e.g. [n>=0])
assume stapool_vt (a:t@ype, n:int, m:int, l:addr) = @(
  (array_v (a, l, n), array_v (a?, l + n*sizeof(a), m-n) | ptr (l + n*sizeof(a)))
, size_t m
, ptr l
) (* end of [buf_vt] *)
//
assume pptr (a:t@ype, l:addr) = [n,m:nat;l1:addr] (
  {n1:nat | n <= n1; n1 <= m} () -<> vsubw_p (a @ l1, array_v (a, l, n1))
, int n
, int m
| ptr l1
) (* end of [pptr] *)
//
in (* of [local] *)
//
implement{a}
stapool_init {n} {l} (pf_bytes | p, n, buf) = () where {
  prval () = lemma_array_v_param {a?} (pf_bytes)
  prval () = $effmask_wrt (buf.0.0 := array_v_nil {a} ())
  prval () = $effmask_wrt (buf.0.1 := pf_bytes)
  val () = buf.0.2 := p
  val () = buf.1 := n
  val () = buf.2 := p
} (* end of [stapool_init] *)
//
primplement
stapool_free {a} {m,n} {l} (buf) = let
//
val (pf1_arr, pf2_arr) = (buf.0.0, buf.0.1)
//
prval pf1_arr = __trustme {a} (pf1_arr) where {
  // can be proven by induction over [n] using [topize]
  extern
  prval __trustme : {a:t@ype} {l:addr} {n:int} array_v (INV(a), l, n) -<> array_v (a?, l, n)
} // end of [prval]
//
in
  array_v_unsplit {a?} (pf1_arr, pf2_arr)
end // end of [stapool_free]
//
implement{a}
stapool_is_full {n,m} {l} (buf) = let
//
extern
castfn
lemma1 : {lb:addr;a,b:nat} (bool (lb+a < lb+b)) -> bool (a < b)
//
extern
castfn
lemma2 : {a:pos;x,y:nat} (bool (x*a < y*a)) -> bool (x < y)
//
extern
prval lemma3 : {a:t@ype} () -> [sizeof(a) == sizeof(a?)] void
//
extern
prval lemma4 : () -<> [sizeof(a) > 0] void
//
val p_end = ptr1_add_guint<a> (buf.2, buf.1)
val res = buf.0.2 < p_end // buf.1 < buf.2
//
prval () = lemma4 () // in general, [a] could be [void] (of size 0), but that is unusable
prval () = lemma_array_v_param {a} (buf.0.0)
prval () = lemma_array_v_param {a?} (buf.0.1)
prval () = mul_gte_gte_gte {n,sizeof(a)} ()
prval () = mul_gte_gte_gte {m,sizeof(a)} ()
val res = lemma1 {l,n*sizeof(a),m*sizeof(a)} (res)
val res = lemma2 {sizeof(a),n,m} (res)
//
in
//
res
//
end // end of [stapool_is_full]
//
implement{a}
stapool_alloc {n,m} {l} (buf, x) = let
  prval pf1_arr = buf.0.0
  prval (pf1_at, pf2_arr) = array_v_uncons {a?} {l+n*sizeof(a)} (buf.0.1)
  val p = buf.0.2
  prval [l1:addr] EQADDR () = eqaddr_make_ptr (p)
  val () = ptr_set<a> (pf1_at | p, x)
  //
  prval () = lemma_array_v_param (pf1_arr)
  prval n = praxi_int{n} ()
  prval m = praxi_int{m} ()
  prval pf = __trustme where {
    // can be derived if needed
    extern
    prval __trustme : {n1:nat | n <= n1; n1 <= m} () -<> vsubw_p (a @ l1, array_v (a, l, n1))
  }
  //
  val () = buf.0.2 := ptr1_succ (p)
//  val () = buf.1 := succ (buf.1)
  prval pf1_arr = array_v_extend (pf1_arr, pf1_at)
  // why does it complain about wrt effect?
  prval () = $effmask_wrt (buf.0.0 := pf1_arr)
  prval () = $effmask_wrt (buf.0.1 := pf2_arr)
in
  #[n,m,l1 | (pf, n, m | p)]
end // end of [stapool_alloc]
//
implement{a}
pptr_read {n1,m1} {l} (buf, r) = let
//
val (pf_sub, n, m | p) = r
prval [n:int] EQINT () = eqint_make_gint (n)
prval [m:int] EQINT () = eqint_make_gint (m)
//
extern
prval lemma1 (): [n <= n1; n1 <= m] void // NOTE: we never "unbump" the pointer
//
extern
prval lemma2 (): [m1 == m] void
//
prval () = lemma1 ()
prval () = lemma2 ()
//  
prval pf_sub0 = pf_sub {n1} ()
//
prval fpf0 = vsubw_elim (pf_sub0)
prval (pf_at, fpf1) = fpf0 (buf.0.0)
val res = ptr_get<a> (pf_at | p)
prval () = $effmask_wrt (buf.0.0 := fpf1 (pf_at))
//
in
//
res
//
end // end of [pptr_read]
//
implement{a}
pptr_write {n1,m1} {l} (buf, r, x) = let
//
val (pf_sub, n, m | p) = r
prval [n:int] EQINT () = eqint_make_gint (n)
prval [m:int] EQINT () = eqint_make_gint (m)
//
extern
prval lemma1 (): [n <= n1; n1 <= m] void // NOTE: we never "unbump" the pointer
//
extern
prval lemma2 (): [m1 == m] void
//
prval () = lemma1 ()
prval () = lemma2 ()
//  
prval pf_sub0 = pf_sub {n1} ()
//
prval fpf0 = vsubw_elim (pf_sub0)
prval (pf_at, fpf1) = fpf0 (buf.0.0)
val () = ptr_set<a> (pf_at | p, x)
prval () = $effmask_wrt (buf.0.0 := fpf1 (pf_at))
//
in
end // end of [pptr_write]
//
end (* of [local] *)
//

(* ****** end of [stapool.dats] ****** *)

// issues with stapool:
// - freeing up the array

(* ****** ****** *)

fun
do_other_stuff (): void = let
//
val () = println!("do other stuff: start")
//
// NOTE: no dynamic memory allocation!
//
#define BUFSZ 512
var arr: @[int][BUFSZ] // uninitialized
val p_arr = addr@(arr)
//
var pool: stapool_vt0 (int) // uninitialized
val p1_arr = p_arr
val () = stapool_init<int> (view@(arr) | p1_arr, (i2sz)BUFSZ, pool)
//
val ref1 = stapool_alloc<int> (pool, 1)
val ref2 = stapool_alloc<int> (pool, 2)
val ref3 = stapool_alloc<int> (pool, 3)
//
val () = println!("ref1 = ", pptr_read<int> (pool, ref1), ", ref2 = ", pptr_read<int> (pool, ref2))
val () = pptr_write<int> (pool, ref2, 5)
val () = println!("ref2 = ", pptr_read (pool, ref2))
//
prval () = view@(arr) := stapool_free (pool)
//
val () = println!("do other stuff: completed")
//
in
end // end of [do_other_stuff]

(* ****** ****** *)

implement
main0 () = {
  val () = do_stuff ()
  val () = do_other_stuff ()
}
