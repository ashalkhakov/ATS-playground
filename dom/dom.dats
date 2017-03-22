(*
** Hello, world!

http://www.doc.ic.ac.uk/~gds/papers/extendedpods2008.pdf
*)

(* ****** ****** *)

#include
"share/atspre_staload.hats"

(* ****** ****** *)

// of unknown node type (element, text, etc.)
absview
domnode_v (
  h:int (*height*)
, lp:addr (*parent pointer*)
, lb:addr (*backward pointer*)
, lf:addr (*forward pointer*)
, lc:addr(*child pointer*)
, l:addr (*self pointer*)
) // end of [domnode_v]

extern
prfun
domnode_v_lemma {h:int} {lp,lb,lf,lc,l:addr}
  (!domnode_v (h, lp, lb, lf, lc, l)):<> [l > null] void

viewdef domnode_v (h:int, lp:addr, lb:addr, lf:addr, l:addr) = [lc:addr]
  domnode_v (h, lp, lb, lf, lc, l)
// end of [domnode_v]

// some functions on nodes
extern
prfun
domnode_ptr_is_gtz
  {h:int} {l,lp,lb,lf,lc,lp:addr}
  (pf: !domnode_v (h, lp, lb, lf, l)): [l > null] void
// end of [domnode_ptr_is_gtz]

extern
fun{}
domnode_get_parent {h:int} {lp,lb,lf,l0:addr} (
  !domnode_v (h, lp, lb, lf, l0) | ptr l0
) : ptr lp

extern
fun{}
domnode_set_parent {h:int} {l0,lb,lf,lp,lp1:addr} (
  !domnode_v (h, lp, lb, lf, l0) >> domnode_v (h, lp1, lb, lf, l0)
| ptr l0, ptr lp1
) : void

extern
fun{}
domnode_get_prev {h:int} {lp,lb,lf,l0:addr} (
  !domnode_v (h, lp, lb, lf, l0) | ptr l0
) : ptr lb

extern
fun{}
domnode_set_prev {h:int} {l0,lb,lb1,lf,lp:addr} (
  !domnode_v (h, lp, lb, lf, l0) >> domnode_v (h, lp, lb1, lf, l0)
| ptr l0, ptr lb1
) : void


extern
fun{}
domnode_get_next {h:int} {lp,lb,lf,l0:addr} (
  !domnode_v (h, lp, lb, lf, l0) | ptr l0
) : ptr lf

extern
fun{}
domnode_set_next {h:int} {l0,lb,lf,lf1,lp:addr} (
  !domnode_v (h, lp, lb, lf, l0) >> domnode_v (h, lp, lb, lf1, l0)
| ptr l0, ptr lf1
) : void

extern
fun{}
domnode_get_child {h:int} {lp,lb,lf,lc,l0:addr} (
  !domnode_v (h, lp, lb, lf,lc, l0) | ptr l0
) : ptr lc

extern
fun{}
domnode_set_child {h:int} {l0,lb,lf,lc,lc1,lp:addr} (
  !domnode_v (h, lp, lb, lf, lc, l0) >> domnode_v (h, lp, lb, lf, lc1, l0)
| ptr l0, ptr lc1
) : void

(*
// node type
datatype node_type = NTtext | NTelem
extern
fun{}
domnode_get_type {h:int} {lp,lb,lf,l:addr} (
  !domnode_v (h, lb, lf, lp, l)
| ptr l
) : node_type
*)

dataview
domdlfseg_v ( // forward segment (left to right, traverse by next ptr)
  int(*size of segment*)
, int(*height*)
, addr(*leftmost*)
, addr(*prev of leftmost*)
, addr(*rightmost*)
, addr(*next of rightmost*)
, addr(*parent*)
) =
  | {n,h,hl:nat}
    {lf,lfp:addr | lf > null}
    {lr,lrn:addr}
    {lfn:addr}
    {lp:addr}
    domdlfseg_v_cons (n+1, max(h,hl), lf, lfp, lr, lrn, lp) of (
      domtree_v (h, lp, lf, lfp, lfn), domdlfseg_v (n, hl, lfn, lf, lr, lrn, lp)
    ) // end of [domdlfseg_v_cons]
  | {lf:addr}
    {lr:addr}
    {lp:addr}
    domdlfseg_v_nil (0, 0, lf, lr, lr, lf, lp) of ()
// end of [domdlfseg_v]

and
domdlrseg_v ( // reverse segment (right to left, traverse by prev ptr)
  int(*size*)
, int(*height*)
, addr(*leftmost*)
, addr(*prev of leftmost*)
, addr(*rightmost*)
, addr(*next of rightmost*)
, addr(*parent*)
) =
  | {n,h,hr:nat}
    {lf,lfp:addr}
    {lr,lrn:addr | lr > null}
    {lrp:addr}
    {lp:addr}
    domdlrseg_v_cons (n+1, max(h,hr), lf, lfp, lr, lrn, lp) of (
      domdlrseg_v (n, hr, lf, lfp, lrp, lr, lp), domtree_v (h, lp, lr, lrp, lrn)
    ) // end of [domdlrseg_v_cons]
  | {lf:addr}
    {lr:addr}
    {lp:addr}
    domdlrseg_v_nil (0, 0, lf, lr, lr, lf, lp) of ()
// end of [domdlrseg_v]

and
domtree_v (
  int(*height*)
, addr(*parent*)
, addr(*self*)
, addr(*prev*)
, addr(*next*)
, addr(*first child*)
) =
  // Element node or Text node
  | {lp,lb,lf,lm,lr:addr}
    {hr:nat;h:int | h == 1+hr}
    {nr:int}
    {slf:agz}
    Node (h, lp, slf, lb, lf, lm) of (
      // tree node
      domnode_v (h, lp, lb, lf, lm, slf)
      // doubly-linked list of children (pointer to the first element of the list)
    , domdlfseg_v (nr, hr, lm, null, lr, null, slf)
    ) // end of [Node]
  // Empty subtree
  | {lp,lr,lf:addr} Empty (0, lp, null, lr, lf, null)
// end of [dataview domtree_v]

where domtree_v (h:int, lp:addr, l:addr, lb:addr, lf:addr) =
  [lc:addr] domtree_v (h, lp, l, lb, lf, lc)

// https://github.com/ashalkhakov/ATS-Lang/blob/master/libats/ngc/DATS/linmap_pavltree.dats

// domdiff_v is essentially the current state of traversal
// of the DOM tree: DIFFnode is the "hole", or the parent of the focussed/selected
// node of the tree
dataview domdiff_v (
  (*height*)int
, (*missing subtree height*)int
, (*child: root of the missing domtree*)addr
, (*prev sibling of child*)addr
, (*next sibling of child*)addr
, (*index of child in the forest of parent's children*)int
, (*total number of parent's children*)int
, (*root*)addr
, (*root parent*)addr
, (*self*)addr
) = (* view for a domtree minus a sub domtree *)
  | {n,h:nat | h <= n}
    {hf,hr,hs:nat | hs <= h; h==max(hf,max(hs,hr))+1}
    {nf,nr:nat} {lf,lmp,lm,lmn,lr:addr}
    {slfp,slfn,slfc:addr}
    {pnt:addr} {dir,nr1:nat} {rt,rtp:addr}
    {slf:agz;slfp,slfn:addr}
    DIFFnode (n, hs, lm, lmp, lmn, nf, nr, rt, rtp, slf) of (
    // node: parent, prev, next, children, self pointers
      domnode_v (h, pnt, slfp, slfn, lf, slf)
    // siblings to the left of [lm] (following prev pointers)
    , domdlrseg_v (nf, hf, lf, null, lmp, lm, slf)
    // siblings to the right of [slf] (following next pointers)
    , domdlfseg_v (nr, hr, lmn, lm, lr, null, slf)
    // path upwards to the root
    , domdiff_v (n, h, slf, slfp, slfn, dir, nr1, rt, rtp, pnt)
    ) // end of [DIFFnode]
  | {h:nat} {chld:addr} {dir:nat} {slf:addr}
    DIFFemp (h, h, chld, null, null, dir, dir, chld, slf, slf) of ()
// end of [domdiff_v]

//
extern
prfun
domdlrseg_v_append_domdlfseg_v {hf,hr:nat} {nf:nat;nr:pos} {lf,lm,lmp,lr,lp:addr} (
  domdlrseg_v (nf, hf, lf, null, lmp, lm, lp)
, domdlfseg_v (nr, hr, lm, lmp, lr, null, lp)
): domdlfseg_v (nf+nr, max(hf,hr), lf, null, lr, null, lp)
//
primplement
domdlrseg_v_append_domdlfseg_v {hf,hr} {nf,nr} {lf,lm,lmp,lr,lp} (
  pf_rdl
, pf_fdl
) = let
//
fun
loop {hf,hr:nat} {nf:nat;nr:pos} {lf,lm,lmp,lr,lp,lfp,lrn:addr} .<nf>. (
  pf_rdl: domdlrseg_v (nf, hf, lf, lfp, lmp, lm, lp)
, pf_fdl: domdlfseg_v (nr, hr, lm, lmp, lr, lrn, lp)
):<prf> domdlfseg_v (nf+nr, max(hf,hr), lf, lfp, lr, lrn, lp) = (
//
case+ pf_rdl of
| domdlrseg_v_cons (pf1_rdl, pf_t) => loop (pf1_rdl, domdlfseg_v_cons (pf_t, pf_fdl))
| domdlrseg_v_nil () => pf_fdl
//
) (* end of [loop] *)
//
in
  loop (pf_rdl, pf_fdl)
end // end of [domdlrseg_v_append_domdlfseg_v]

prfun
domdiff_domtree_join
  {n,h:nat | h <= n}
  {chld,chldp,chldn:addr | chld > null}
  {dir,nr:nat} {rt,rtp,slf:addr} .<n-h>. (
    fpf: domdiff_v (n, h, chld, chldp, chldn, dir, nr, rt, rtp, slf)
  , pf0: domtree_v (h, slf, chld, chldp, chldn)
  ) :<> domtree_v (n, rtp, rt, null, null) =
  case+ fpf of
  | DIFFnode (pf_at, pfr, pff, fpf) => let
        prval pf00 = domdlfseg_v_cons (pf0, pff)
        prval pf1 = domdlrseg_v_append_domdlfseg_v (pfr, pf00)
        prval pf1_at = Node (pf_at, pf1)
    in
        domdiff_domtree_join (fpf, pf1_at)
    end // end of [Node1]
  | DIFFemp () => pf0
// end of [domdiff_domtree_join]

prfun
domdiff_takeout
  {n,h:int} {chld,chldp,chldn:addr} {dir,nr:int} {rt,rtp:addr}
  {slf:addr | slf <> rtp} .< >. (
    pf: domdiff_v (n, h, chld, chldp, chldn, dir, nr, rt, rtp, slf)
  ) :<> [h0:int;pnt,slfp,slfn,lc:addr] (
    domnode_v (h0, pnt, slfp, slfn, lc, slf)
  , domnode_v (h0, pnt, slfp, slfn, lc, slf)
      -<lin,prf> domdiff_v (n, h, chld, chldp, chldn, dir, nr, rt, rtp, slf)
  ) = let
      prval DIFFnode (pf_at, pfr, pff, fpf) = pf
    in
      #[.. | (pf_at, llam (pf_at) => DIFFnode (pf_at, pfr, pff, fpf))]
    end // end of [domdiff_takeout]

// the type of a rooted tree
viewdef domtree_v_root (h:int, l:addr) = domtree_v (h, null, l, null, null)

// ------------------------

// TODO: these functions are easiest to implement externally in C
extern
fun
domdlfseg_ptr_is_cons
  {n,h:int} {lf,lfp,lr,lrn,lp:addr} (
  !domdlfseg_v (n, h, lf, lfp, lr, lrn, lp) | ptr lf
) :<> [n > 0 && lf > null; n == 0 && lf == null] bool (n > 0) // just checks for null
extern
prfun
domdlfseg_is_cons
  {n,h:int} {lf,lfp,lr,lrn,lp:addr | lf > null} (
  !domdlfseg_v (n, h, lf, lfp, lr, lrn, lp)
) :<> [n > 0] void
extern
fun
domdlrseg_ptr_is_cons
  {n,h:int} {lf,lfp,lr,lrn,lp:addr} (
  !domdlrseg_v (n, h, lf, lfp, lr, lrn, lp) | ptr lr
) :<> [n > 0 && lf > null; n == 0 && lf == null] bool (n > 0) // just checks for null
// ------------------------

absvt@ype domnav_vt (
  int(*tree height*)
, int(*missing subtree height*)
, int(*children to the left of focussed node*)
, int(*children to the right of focussed node*)
, addr(*root*)
, addr(*parent of root*)
, addr(*parent of missing subtree*)
, addr(*missing subtree*)
, addr(*first child of missing subtree*)
) = @{p_rtp= ptr, p_root= ptr, p_slf= ptr, p_chld= ptr}
vtypedef domnav_vt0 =
  domnav_vt (0, 0, 0, 0, null, null, null, null, null)?
vtypedef domnav_vt (n:int, h:int, nf:int, nr:int, rt:addr, rtp:addr, slf:addr, chld:addr) =
  [desc:addr] domnav_vt (n, h, nf, nr, rt, rtp, slf, chld, desc)

// TODO: generalize nav_beg and nav_end (we can start navigation at any non-null
// node!)
// begin traversal (during which you retain the parent and the focussed child pointers...
// but you may also want to retain the root pointer too!
extern
fun
domtree_nav_beg {h:nat} {rt:agz} (
  domtree_v_root (h, rt)
| p: ptr rt
, tr: &domnav_vt0 >> domnav_vt (h, h, 0, nr, rt, null, slf, chld)
): #[slf,chld:addr;nr:nat] void
//
// end traversal
extern
fun
domtree_nav_end {n,h:nat | h <= n} {dir,nr:int} {slf,chld,rt,rtp:addr} (
  &domnav_vt (n, h, dir, nr, rt, rtp, slf, chld) >> domnav_vt0
): [rtp:addr;lb,lf:addr] (
  domtree_v (n, rtp, rt, lb, lf)
| ptr rt
) (* end of [domtree_nav_end] *)
//
// checks if the focussed tree has at least one child
extern
fun
domtree_nav_has_child {n,h,dir,nr:int} {rt,rtp,slf,chld,desc:addr} (
  &domnav_vt (n, h, dir, nr, rt, rtp, slf, chld, desc)
): bool (desc > null)
// moves to the first child of the focussed node
extern
fun
domtree_nav_child {n,h,dir,nr:int} {rt,rtp,slf:addr;chld,desc:addr | desc > null} (
  &domnav_vt (n, h, dir, nr, rt, rtp, slf, chld, desc)
    >> domnav_vt (n, h1, 0, nr1, rt, rtp, chld, chld1)
): #[chld1:addr] #[h1:nat | h1 <= h] #[nr1:int] void
//
// moves up to the parent node
extern
fun
domtree_nav_parent {n,h,dir,nr:int} {rt,rtp,slf,chld:addr | slf <> rtp} (
  &domnav_vt (n, h, dir, nr, rt, rtp, slf, chld)
    >> domnav_vt (n, h1, dir1, nr1, rt, rtp, slf1, slf)
): #[dir1,nr1,h1:nat | h <= h1; h1 <= n] #[slf1:addr] void
// checks if the focussed node has a parent
extern
fun
domtree_nav_has_parent {n,h,dir,nr:int} {rt,rtp,slf,chld:addr} (
  &domnav_vt (n, h, dir, nr, rt, rtp, slf, chld)
): bool (slf <> rtp)
//
// checks if the focussed node has a following sibling
extern
fun
domtree_nav_has_next {n,h,dir,nr:int} {rt,rtp,slf,chld:addr | slf <> rtp} (
  &domnav_vt (n, h, dir, nr, rt, rtp, slf, chld)
): bool (nr > 0)
// moves to the following sibling
extern
fun
domtree_nav_next {n,h,dir,nr:int | nr > 0} {rt,rtp,slf,chld:addr | slf <> rtp} (
  &domnav_vt (n, h, dir, nr, rt, rtp, slf, chld)
    >> domnav_vt (n, h1, dir+1, nr-1, rt, rtp, slf, chld1)
): #[h1:nat | h1 <= n] #[chld1:addr] void
// checks if the focussed node has a following sibling
extern
fun
domtree_nav_has_prev {n,h,dir,nr:int} {rt,rtp,slf,chld:addr | slf <> rtp} (
  &domnav_vt (n, h, dir, nr, rt, rtp, slf, chld)
): bool (dir > 0)
// moves to the preceding sibling
extern
fun
domtree_nav_prev {n,h,dir,nr:int | dir > 0} {rt,rtp,slf,chld:addr | slf <> rtp} (
  &domnav_vt (n, h, dir, nr, rt, rtp, slf, chld)
    >> domnav_vt (n, h1, dir-1, nr+1, rt, rtp, slf, chld1)
): #[h1:nat | h1 <= n; dir-1 >= 0] #[chld1:addr] void
//
// domtree_nav_takeout: for taking out the focussed node
(*
assume domnav_vt (n:int, h:int, dir:int, nr:int, rt:addr, rtp:addr, slf:addr, chld:addr, desc:addr) = @{
  p_rtp= ptr rtp
, p_root= ptr rt
, p_slf= ptr slf
, p_chld= ptr chld
, pf_valid = param_validity (n, h, dir, nr, chld)
, pf_ctx = [chldp,chldn:addr] (
    domdiff_v (n, h, chld, chldp, chldn, dir, nr, rt, rtp, slf)
  , domtree_v (h, slf, chld, chldp, chldn, desc)
  )
} (* end of [domnav_vt] *)
// what if we just allow the user do something with the node? (via a fntmplt)
// - the user must NOT deallocate the node...
// - the quality of types will suffer greatly (the user will be unable to figure out where they are...)
// ok, what if we give them both domdiff and the domtree? that should work!

extern
fun
// what type to give to the domtraversal?
domtree_nav_takeout {n,h,dir,nr:int} {rt,rtp,slf,chld,desc:addr} (
  &domnav_vt (n, h, dir, nr, rt, rtp, slf, chld) >> domtraversal0_vt?
) : (domtree_v (?), domtraversal0_vt? >> dom | ptr ?)
*)
//
(* ****** ****** *)
//
local
//
dataview param_validity (int, int, int, int, addr) =
  {n,h:nat | h <= n} {dir,nr:nat} {chld:agz}
  param_validity_v (n, h, dir, nr, chld)
//
assume domnav_vt (n:int, h:int, dir:int, nr:int, rt:addr, rtp:addr, slf:addr, chld:addr, desc:addr) = @{
  p_rtp= ptr rtp
, p_root= ptr rt
, p_slf= ptr slf
, p_chld= ptr chld
, pf_valid = param_validity (n, h, dir, nr, chld)
, pf_ctx = [chldp,chldn:addr] (
    domdiff_v (n, h, chld, chldp, chldn, dir, nr, rt, rtp, slf)
  , domtree_v (h, slf, chld, chldp, chldn, desc)
  )
} (* end of [domnav_vt] *)
//
in // in of [local]
//
implement
domtree_nav_beg {h} {rt} (
  pf_dom
| p_root, tr
) = let
  val () = tr.p_rtp := the_null_ptr
  val () = tr.p_slf := the_null_ptr
  val () = tr.p_root := p_root
  val () = tr.p_chld := p_root
  (* FIXME: why is masking necessary? why is proof assignment effectful? *)
  prval () = $effmask_wrt (tr.pf_valid := param_validity_v ())
  prval () = $effmask_wrt (tr.pf_ctx := (DIFFemp (), pf_dom))
in
  (*void*)
end // end of [domtree_nav_beg]
//
implement
domtree_nav_end {n,h} {dir,nr} {slf,chld,rt,rtp} (
  tr
) = let
  prval param_validity_v () = tr.pf_valid
  prval (pf_diff, pf_dom) = tr.pf_ctx
  val p_root = tr.p_root
  prval pf_tree = domdiff_domtree_join (pf_diff, pf_dom)
in
  (pf_tree | p_root)
end // end of [domtree_nav_end]
//
implement
domtree_nav_has_child {n,h,dir,nr} {rt,rtp,slf,chld,desc} (tr) = let
//
prval param_validity_v () = tr.pf_valid
prval (pf_diff, pf_tree) = tr.pf_ctx
//
val p_chld = tr.p_chld
val p_slf = tr.p_slf
//
prval Node (pf_at, pf_seg) = pf_tree
val p_chld1 = domnode_get_child (pf_at | p_chld)
val res0 = domdlfseg_ptr_is_cons (pf_seg | p_chld1)
val res1 = p_chld1 > the_null_ptr
prval pf_tree = Node (pf_at, pf_seg)
//
prval () = $effmask_wrt (tr.pf_valid := param_validity_v ())
prval () = $effmask_wrt (tr.pf_ctx := (pf_diff, pf_tree))
//
in
//
res1
//
end // end of [domtree_nav_has_child]
//
implement
domtree_nav_child {n,h,dir,nr} {rt,rtp,slf,chld,desc} (tr) = {
//
prval param_validity_v () = tr.pf_valid
prval (pf_diff, pf_tree) = tr.pf_ctx
//
val p_chld = tr.p_chld
prval Node (pf_at, pf_seg) = pf_tree
val p_chld1 = domnode_get_child (pf_at | p_chld)
val () = tr.p_slf := tr.p_chld
val () = tr.p_chld := p_chld1
//
prval () = domdlfseg_is_cons (pf_seg)
//
prval pf_rseg = domdlrseg_v_nil ()
prval domdlfseg_v_cons (pf1_tree, pf_fseg) = pf_seg
prval pf1_diff = DIFFnode (pf_at, pf_rseg, pf_fseg, pf_diff)
prval () = $effmask_wrt (tr.pf_valid := param_validity_v ())
prval () = $effmask_wrt (tr.pf_ctx := (pf1_diff, pf1_tree))
//
} (* end of [domtree_nav_child] *)
//
implement
domtree_nav_has_parent {n,h,dir,nr} {rt,rtp,slf,chld} (tr) = let
//
prval param_validity_v () = tr.pf_valid
//
val res = tr.p_slf <> tr.p_rtp
//
prval () = $effmask_wrt (tr.pf_valid := param_validity_v ())
//
in
  res
end // end of [domtree_nav_has_parent]
//
implement
domtree_nav_parent {n,h,dir,nr} {rt,rtp,slf,chld} (tr) = {
//
prval param_validity_v () = tr.pf_valid
prval (pf_diff, pf_tree) = tr.pf_ctx
//
val p_chld = tr.p_chld
val p_slf = tr.p_slf
//
prval DIFFnode (pf1_at, pf1_rseg, pf1_fseg, pf1_diff) = pf_diff
val p_slf1 = domnode_get_parent (pf1_at | p_slf)
//
val () = tr.p_chld := p_slf
val () = tr.p_slf := p_slf1
//
prval pf1_seg = domdlrseg_v_append_domdlfseg_v (pf1_rseg, domdlfseg_v_cons (pf_tree, pf1_fseg))
prval pf1_tree = Node (pf1_at, pf1_seg)
//
prval () = $effmask_wrt (tr.pf_valid := param_validity_v ())
prval () = $effmask_wrt (tr.pf_ctx := (pf1_diff, pf1_tree))
//
} (* end of [domtree_nav_parent] *)
//
implement
domtree_nav_has_next {n,h,dir,nr} {rt,rtp,slf,chld} (tr) = let
//
prval param_validity_v () = tr.pf_valid
prval (pf_diff, pf_tree) = tr.pf_ctx
//
val p_chld = tr.p_chld
val p_slf = tr.p_slf
//
prval DIFFnode (pf1_at, pf1_rseg, pf1_fseg, pf1_diff) = pf_diff
//
prval Node (pf_at, pf_seg) = pf_tree
val p_chld1 = domnode_get_next (pf_at | p_chld)
prval pf_tree = Node (pf_at, pf_seg)
//
val res = domdlfseg_ptr_is_cons (pf1_fseg | p_chld1)
//
prval pf2_diff = DIFFnode (pf1_at, pf1_rseg, pf1_fseg, pf1_diff)
//
prval () = $effmask_wrt (tr.pf_valid := param_validity_v ())
prval () = $effmask_wrt (tr.pf_ctx := (pf2_diff, pf_tree))
//
in
//
res
//
end // end of [domtree_nav_has_next]
//
implement
domtree_nav_next {n,h,dir,nr} {rt,rtp,slf,chld} (tr) = {
//
prval param_validity_v () = tr.pf_valid
prval (pf_diff, pf_tree) = tr.pf_ctx
//
val p_chld = tr.p_chld
val p_slf = tr.p_slf
//
prval DIFFnode (pf1_at, pf1_rseg, pf1_fseg, pf1_diff) = pf_diff
//
prval Node (pf_at, pf_seg) = pf_tree
val p_chld1 = domnode_get_next (pf_at | p_chld)
prval pf_tree = Node (pf_at, pf_seg)
//
val () = tr.p_chld := p_chld1
//
prval pf1_rseg = domdlrseg_v_cons (pf1_rseg, pf_tree)
prval domdlfseg_v_cons (pf1_tree, pf1_fseg) = pf1_fseg
//
prval pf2_diff = DIFFnode (pf1_at, pf1_rseg, pf1_fseg, pf1_diff)
//
prval () = $effmask_wrt (tr.pf_valid := param_validity_v ())
prval () = $effmask_wrt (tr.pf_ctx := (pf2_diff, pf1_tree))
//
} (* end of [domtree_nav_next] *)
//
implement
domtree_nav_has_prev {n,h,dir,nr} {rt,rtp,slf,chld} (tr) = let
//
prval param_validity_v () = tr.pf_valid
prval (pf_diff, pf_tree) = tr.pf_ctx
//
val p_chld = tr.p_chld
val p_slf = tr.p_slf
//
prval DIFFnode (pf1_at, pf1_rseg, pf1_fseg, pf1_diff) = pf_diff
//
prval Node (pf_at, pf_seg) = pf_tree
val p_chld1 = domnode_get_prev (pf_at | p_chld)
prval pf_tree = Node (pf_at, pf_seg)
//
val res = domdlrseg_ptr_is_cons (pf1_rseg | p_chld1)
//
prval pf2_diff = DIFFnode (pf1_at, pf1_rseg, pf1_fseg, pf1_diff)
//
prval () = $effmask_wrt (tr.pf_valid := param_validity_v ())
prval () = $effmask_wrt (tr.pf_ctx := (pf2_diff, pf_tree))
//
in
//
res
//
end // end of [domtree_nav_has_prev]
//
implement
domtree_nav_prev {n,h,dir,nr} {rt,rtp,slf,chld} (tr) = {
//
prval param_validity_v () = tr.pf_valid
prval (pf_diff, pf_tree) = tr.pf_ctx
//
val p_chld = tr.p_chld
val p_slf = tr.p_slf
//
prval DIFFnode (pf1_at, pf1_rseg, pf1_fseg, pf1_diff) = pf_diff
//
prval Node (pf_at, pf_seg) = pf_tree
val p_chld1 = domnode_get_prev (pf_at | p_chld)
prval pf_tree = Node (pf_at, pf_seg)
//
val () = tr.p_chld := p_chld1
//
prval domdlrseg_v_cons (pf1_rseg, pf1_tree) = pf1_rseg
prval pf1_fseg = domdlfseg_v_cons (pf_tree, pf1_fseg)
//
prval pf2_diff = DIFFnode (pf1_at, pf1_rseg, pf1_fseg, pf1_diff)
//
prval () = $effmask_wrt (tr.pf_valid := param_validity_v ())
prval () = $effmask_wrt (tr.pf_ctx := (pf2_diff, pf1_tree))
//
} (* end of [domtree_nav_prev] *)

end // end of [local]

// what to do now?
// 1. write basic navigation functions (e.g. move to first child, move to next/prev sibling)
//    - we still might have to amend our definitions once more, to support the next/prev pointers
//      - done! i think i got definitions right...
//    - done!
//    - let's strengthen the type of nav_beg/nav_end?
// 2. write the split function, which finds the node by predicate,
//    splitting it along the way (based on pavltree_split)
//    - what about *many* results? this is kind of like a doubly-linked
//      list of nodes that point back into the tree nodes
//      that satisfy the predicate (a "front" through the tree)
//    - working on it!
// 3. write DOM manipulation functions from minimal DOM
//    - appendChild
//    - removeChild
//    - createNode
//    - createTextNode
//    - getChildNodes (this does a split! so you get the cake and eat it too)
// 4. wire it up to JS and try to do some real stuff

////
// TODO: this should actually be some user-defined type... right?
extern
fun{} domtree_split$fwork {l:addr} (ptr l): int

extern
fun{}
domtree_split {h0:nat} {rt:addr} (
  pf: domtree_v_root (h0, rt)
| p: &ptr rt >> ptr slf
, dir: &int 0 >> int dir
// NOTE: this interface assumes ONE result, while we want MANY results...
// iterators anybody? ...
// basically, if we get some traversal state in return, we can ask for more
// results... so, diff+subtree needs to be put into a new zipper-esque type
// which will allow to navigate freely
// - yeah, we can just code up some basic navigation primitives, this is easier I think
//   - based on the primitives, the split function can be implemented
//   - start navigation at root (given a rooted tree, outputs a traversal state)
//   - move to the first child of node
//   - move to the next/previous sibling of node
//   - move up to the parent
// - what about stable node identities? we would like to retain pointers
//   to the inside of the tree, BUT the pointers have to be intelligently maintained
//   (e.g., if a node is deleted, all pointers to it must be invalidated)
) :<> #[dir:nat;slf:addr] [h1:nat | h1 <= h0;chld,chldn,chldp:addr] (
  domdiff_v (h0, h1, chld, chldp, chldn, dir, rt, null, slf)
, domtree_v (h1, slf, chld, chldp, chldn)
| ptr chld
) (* end of [domtree_split] *)
////
implement{}
domtree_split {h0} {rt} (
  pf
| p, dir
) = let
//
fun loop {h:nat | h <= h0} {chld:addr} {dir:two} {slf:addr} .<h>. (
  fpf: pavldiff_v (key, itm, h0, h, chld, dir, rt, null, slf)
, pf: pavltree_v (key, itm, h, slf, chld)
| p: &ptr slf >> ptr slf, pc: ptr chld, dir: &int dir >> int dir
) :<cloref> #[dir:two;slf:addr] [h1:nat | h1 <= h] [chld:addr] (
  pavldiff_v (key, itm, h0, h1, chld, dir, rt, null, slf)
, pavltree_v (key, itm, h1, slf, chld)
| ptr chld
) = (
//
if pc > null then let
// unpack children
prval Node (pf_at, pf_children) = pf
// see if any of the children is what we want...
val sgn = compare_key_key (k0, pavlnode_get_key<key,itm> (pf_at | pc), cmp)
//
in
//
  if sgn < 0 then let
    val p_tl = pavlnode_get_left<key,itm> (pf_at | pc) in
    p := pc;
    dir := 0(*left*);
    loop (B1L {key,itm} (pf_at, fpf, pf_r), pf_l | p, p_tl, dir)
  end else if sgn > 0 then let
    val p_tr = pavlnode_get_right<key,itm> (pf_at | pc) in
    p := pc;
    dir := 1(*right*);
    loop (B1R {key,itm} (pf_at, pf_l, fpf), pf_r | p, p_tr, dir)
  end else begin // sgn = 0
    (fpf, B (pf_at, pf_l, pf_r) | pc)
  end // end of [if]
//
end else (fpf, pf | pc)
//
) (* end of [loop] *)
//
val pc = p
//
in
//
p := null;
loop (E1 {h0} (), pf | p, pc, dir)
//
end // end of [dom_split]
