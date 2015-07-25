(* ****** ****** *)

#include
"share/atspre_staload.hats"

(* ****** ****** *)
//
sortdef t0p = t@ype
sortdef vt0p = viewt@ype
//
(* ****** ****** *)
//
absview
dlnode_v (
 l: addr, lp: addr, ln: addr // lp: previous; ln: next
) // end of [dlnode_v]
//
prfun
dlnode_ptr_is_gtz
  {l,lp,ln:addr}
  (pf: !dlnode_v (l, lp, ln)): [l > null] void
// end of [dlnode_ptr_is_gtz]
//
(* ****** ****** *)
//
dataview
dlfseg_v (
  int(*len*)
, addr(*leftmost*)
, addr(*prev of leftmost*)
, addr(*rightmost*)
, addr(*next of rightmost*)
) =
  | {n:nat}
    {lf,lfp:addr}
    {lr,lrn:addr}
    {lfn:addr}
    dlfseg_v_cons (n+1, lf, lfp, lr, lrn) of (
      dlnode_v (lf, lfp, lfn), dlfseg_v (n, lfn, lf, lr, lrn)
    ) // end of [dlfseg_v_cons]
  | {lf:addr}
    {lr:addr}
    // why is this cyclic??? lf, lr, lr, lf?
    // because it's a segment! a segment is a portion of a list
    dlfseg_v_nil (0, lf, lr, lr, lf) of ()
// end of [dlfseg_v]

// NOTE: unproven, because to show this, we'd have to always assume and check
// that at-proofs don't alias (and they don't!)
prfun
dlfseg_lemma3 {n:nat} {lf,lfp,lr,lrn:addr} (
  pf_dl: !dlfseg_v (n, lf, lfp, lr, lrn)
):<> [n == 0 && lf == lrn || n > 0 && lf != lrn] void
(*
primplement dlfseg_lemma3 {n} {lf,lfp,lr,lrn} (pf_dl) =
  case pf_dl of
  | dlfseg_v_nil () => let val () = pf_dl := dlfseg_v_nil () in end
  | dlfseg_v_cons (pf_at, pf1_dl) => let val () = pf_dl := dlfseg_v_cons (pf_at, pf1_dl) in end
  *)
(* ****** ****** *)

dataview
dlrseg_v (
  int(*size*)
, addr(*leftmost*)
, addr(*prev of leftmost*)
, addr(*rightmost*)
, addr(*next of rightmost*)
) =
  | {n:nat}
    {lf,lfp:addr}
    {lr,lrn:addr}
    {lrp:addr}
    dlrseg_v_cons (n+1, lf, lfp, lr, lrn) of (
      dlrseg_v (n, lf, lfp, lrp, lr), dlnode_v (lr, lrp, lrn)
    ) // end of [dlrseg_v_cons]
  | {lf:addr}
    {lr:addr}
    dlrseg_v_nil (0, lf, lr, lr, lf) of ()
// end of [dlrseg_v]

(* ****** ****** *)

// API?
// - insert new node after head, or before head
// - fmap (forward or backwards)
// - iterator (begin/end ptrs)
// - deep copy
// - circular list to array and vice versa
// - is_empty, pop front, pop back, takeout the head node for mutation
// - length
// - find first that satisfies a predicate
// - concat two circular lists
// http://www.dcs.bbk.ac.uk/~trevor/FoC/NOTES/notes1%20lists%20p9_13.pdf

// next: what about singly-linked lists? these could also get a similar treatment!
// library of pointer-linked data structures for ATS! also giving users complete
// control over memory layout (this should be QUITE useful for gaming/simulation)

// what about e.g. portals-cells?
// - cells are nodes of a graph
// - portals are arcs connecting two cells
// how to represent that?
// - there can be MANY references to a cell...

(* ****** ****** *)

// forward-navigating circular list: either NULL, or a head element
// followed by up to N elements, ending at the head
dataview dlfcircular_v (int, addr) =
  | {n:nat}
    {lf:agz;lfn,lr:addr}
    dlfcircular_v_some (n+1, lf) of (
      dlnode_v (lf, lr, lfn)
    , dlfseg_v (n, lfn, lf, lr, lf)
    ) (* end of [dlcircular_v_some] *)
  | dlfcircular_v_none (0, null)

(* ****** ****** *)
// functions that every client must implement

// NOTE: this should actually be moved somewhere else, we should not
// dictate to clients the memory layout of the node
vtypedef dlnode0_vt = @{x=int, p=ptr null, n=ptr null}?
vtypedef dlnode_vt (lp:addr, ln:addr) = @{x=int, p=ptr lp, n=ptr ln}

fun dlnode_alloc ():<> [l:addr] (dlnode0_vt @ l, mfree_gc_v (l) | ptr l)
fun dlnode_init {l,lp,ln:addr} (
  mfree_gc_v (l), dlnode0_vt @ l
| ptr l, int, ptr lp, ptr ln
): (dlnode_v (l, lp, ln) | void)
fun dlnode_free {l:addr} (pfgc: mfree_gc_v (l), pfat: dlnode0_vt @ l | p: ptr l):<> void
//
fun
dlnode_ptr_next {l,lp,ln:addr} (!dlnode_v (l, lp, ln) | ptr l): ptr ln
fun
dlnode_ptr_prev {l,lp,ln:addr} (!dlnode_v (l, lp, ln) | ptr l): ptr lp
fun
dlnode_ptr_value {l,lp,ln:addr} (!dlnode_v (l, lp, ln) | ptr l): int
//
fun
dlnode_ptr_free {l,lp,ln:addr} (dlnode_v (l, lp, ln) | ptr l): void
//
fun
fprint_dlnode_ptr {l,lp,ln:addr} (!dlnode_v (l, lp, ln) | FILEref, ptr l): void
//
(* ****** ****** *)
// functions provided by the library

//
fun{}
fprint_dlfcircular$sep (out: FILEref): void
//
fun{}
fprint_dlfcircular {n:int} {l:addr} (!dlfcircular_v (n, l) | out: FILEref, ptr l): void
//
fun{}
fprint_dlfcircular_sep {n:int} {l:addr}
(
  !dlfcircular_v (n, l)
| out: FILEref
, ptr l
, sep: NSH(string)
) : void // end of [fprint_dlfcircular_sep]
//
fun
dlfcircular_ptr_length {n:int} {l:addr} (!dlfcircular_v (n, l) | ptr l): int n
//
fun
dlfcircular_ptr_free {n:int} {l:addr} (dlfcircular_v (n, l) | ptr l): void
//