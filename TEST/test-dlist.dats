#include
"share/atspre_staload.hats"

staload "../SATS/dlist.sats"

local

#define NULL the_null_ptr

// testing!
assume dlnode_v (l: addr, lp: addr, ln: addr) =
  (dlnode_vt (lp, ln) @ l, mfree_gc_v (l))
//
implement
dlnode_ptr_next {l,lp,ln} (pf_at | x) = !x.n
implement
dlnode_ptr_prev {l,lp,ln} (pf_at | x) = !x.p
implement
dlnode_ptr_value {l,lp,ln} (pf_at | x) = !x.x
//
(* ****** ****** *)
//
implement
dlnode_alloc () = let
  val (pf_at, pf_free | p) = ptr_alloc<dlnode0_vt> ()
in
  (pf_at, pf_free | p)
end // end of [dlnode_alloc]
//
implement
dlnode_init {l,lp,ln} (pf_free, pf_at | x, vl, prev, next) = let
  val () = x->p := prev
  val () = x->n := next
  val () = x->x := vl
  prval res = (pf_at, pf_free)
in
  (res | ())
end // end of [dlnode_init]
//
implement
dlnode_free {l} (pfgc, pfat | p) = ptr_free (pfgc, pfat | p)
//
implement
dlnode_ptr_free {l,lp,ln} (pfnod | p) = let
  prval (pf_at, pf_free) = pfnod
in
  dlnode_free (pf_free, pf_at | p)
end // end of [dlnode_ptr_free]
//
implement
fprint_dlnode_ptr {l,lp,ln} (pfnod | out, p) = fprint_int (out, !p.x)
//
in // in of [local]
//
#include "../DATS/dlist.dats"
//
end // end of [local]
(* ****** ****** *)
//
implement
main0 () = let
val (pfw_at, pfw_free | pw) = dlnode_alloc ()
val (pfx_at, pfx_free | px) = dlnode_alloc ()
val (pfy_at, pfy_free | py) = dlnode_alloc ()
val (pfz_at, pfz_free | pz) = dlnode_alloc ()
//
val (pfw_nod | ()) = dlnode_init (pfw_free, pfw_at | pw, 1, pz, px)
val (pfx_nod | ()) = dlnode_init (pfx_free, pfx_at | px, 3, pw, py)
val (pfy_nod | ()) = dlnode_init (pfy_free, pfy_at | py, 5, px, pz)
val (pfz_nod | ()) = dlnode_init (pfz_free, pfz_at | pz, 6, py, pw)
prval () = dlnode_ptr_is_gtz (pfw_nod)
prval () = dlnode_ptr_is_gtz (pfx_nod)
prval () = dlnode_ptr_is_gtz (pfy_nod)
prval () = dlnode_ptr_is_gtz (pfz_nod)
prval foo = dlfcircular_v_some (pfw_nod, dlfseg_v_cons (pfx_nod, dlfseg_v_cons (pfy_nod, dlfseg_v_cons (pfz_nod, dlfseg_v_nil ()))))
//
val () = println!("length: ", dlfcircular_ptr_length (foo | pw))
val () = fprint_dlfcircular_sep (foo | stdout_ref, pw, "; ")
val () = print_newline ()
val () = dlfcircular_ptr_free (foo | pw) // prints 1, 3, then 5, then 6
//
in
  (*void*)
end // end of [main0]

