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
prfun vsubr_intr {v1,v2:view}
(fpf: v2 -<prf> [v:view] (v1, v)): vsubr_p (v1, v2)
// implemented in [vsubrw.dats]
prfun vsubr_elim {v1,v2:view}
(pf: vsubr_p (v1, v2)):<> v2 -<prf> [v:view] (v1, v)
// implemented in [vsubrw.dats]
prfun vsubr_refl {v:view} (): vsubr_p (v, v)

prfun vsubr_trans {v1,v2,v3:view}
(pf12: vsubr_p (v1, v2), pf23: vsubr_p (v2, v3)): vsubr_p (v1, v3)
// end of [vcontain_trans]

prfun vsubr_of_vsubw {v1,v2:view} (pf: vsubw_p (v1, v2)): vsubr_p (v1, v2)

prfun vsubr_tup_2_0 {v0,v1:view} (): vsubr_p (v0, @(v0, v1))

prfun vsubr_tup_2_1 {v0,v1:view} (): vsubr_p (v1, @(v0, v1))
(* ****** ****** *)

prfun vsubw_intr {v1,v2:view}
(fpf: v2 -<prf> (v1, v1 -<lin,prf> v2)): vsubw_p (v1, v2)
// implemented in [vsubrw.dats]

prfun vsubw_elim {v1,v2:view}
(pf: vsubw_p (v1, v2)):<> v2 -<prf> (v1, v1 -<lin,prf> v2)
// implemented in [vsubrw.dats]

prfun vsubw_refl {v:view} (): vsubw_p (v, v)

prfun vsubw_trans {v1,v2,v3:view}
(pf12: vsubw_p (v1, v2), pf23: vsubw_p (v2, v3)): vsubw_p (v1, v3)
(* ****** ****** *)

prfun vsubw_tup_2_0 {v0,v1:view} (): vsubw_p (v0, @(v0, v1))

prfun vsubw_tup_2_1 {v0,v1:view} (): vsubw_p (v1, @(v0, v1))
(* ****** ****** *)

prval vsubw_array_elt :
{a:viewt@ype} {n,i:nat | i < n} {l:addr}
() -<> vsubw_p (a @ l + i*sizeof(a), @[a][n] @ l)

prval vsubw_array_subarray :
{a:viewt@ype} {n0,i,n:nat | i+n <= n0} {l:addr}
() -<> vsubw_p (@[a][n] @ l + i*sizeof(a), @[a][n0] @ l)

(* ****** ****** *)

// abstract view for a region
absview RGN (l0:addr)
// allocate a fresh region to hold the given view

prfun
rgn_alloc {v:view} (!v): [l0:addr] (RGN (l0), vsubw_p (v, RGN (l0)))

// destroy the region
prfun
rgn_free {l0:addr} (RGN (l0)): void

abstype rgnptr (a:addr->t@ype, l0:addr, bool) = ptr
typedef rgnptr (a:addr->t@ype, l0:addr) = [b:bool] rgnptr (a, l0, b)

fun
rgnptr_make_some {a:addr->t@ype} {l,l0:addr}  (vsubw_p (a(l0) @ l, RGN (l0)) | ptr l): rgnptr (a, l0, true)
fun
rgnptr_make_none {a:addr->t@ype} {l0:addr} (): rgnptr (a, l0, false)

castfn
rgnptr_takeout {a:addr->t@ype} {l0:addr} (
  RGN (l0)
| rgnptr (a, l0, true)
): [l:addr] (
  vtakeout (RGN (l0), a(l0) @ l) | ptr l
)

fun
rgnptr_is_some {a:addr->t@ype} {l0:addr} {b:bool} (rgnptr (a, l0, b)): bool b
fun
rgnptr_is_none {a:addr->t@ype} {l0:addr} {b:bool} (rgnptr (a, l0, b)): bool (~b)

fun
eq_rgnptr_rgnptr {a:addr->t@ype} {l0:addr} (rgnptr (a, l0), rgnptr (a, l0)): bool
fun
neq_rgnptr_rgnptr {a:addr->t@ype} {l0:addr} (rgnptr (a, l0), rgnptr (a, l0)): bool
