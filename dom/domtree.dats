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

// node type
datatype node_type = NTtext | NTelem
extern
fun{}
domnode_get_type {h:int} {lp,lb,lf,l:addr} (
  !domnode_v (h, lb, lf, lp, l)
| ptr l
) : node_type

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
    {lf,lfp:addr}
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
    {lr,lrn:addr}
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
) =
  // Element node or Text node
  | {lp,lb,lf,lm,lr:addr}
    {hr:nat;h:int | h == 1+hr}
    {nr:int}
    {slf:agz}
    Node (h, lp, slf, lb, lf) of (
      // tree node
      domnode_v (h, lp, lb, lf, lm, slf)
      // doubly-linked list of children (pointer to the first element of the list)
    , domdlfseg_v (nr, hr, lm, null, lr, null, slf)
    ) // end of [Node]
  // Empty subtree
  | {lp,lr,lf:addr} Empty (0, lp, null, lr, lf)
// end of [dataview domtree_v]

// https://github.com/ashalkhakov/ATS-Lang/blob/master/libats/ngc/DATS/linmap_pavltree.dats

dataview domdiff_v (
  (*height*)int
, (*missing subtree height*)int
, (*child: root of the missing domtree*)addr
, (*prev sibling of child*)addr
, (*next sibling of child*)addr
, (*index of child in the forest of parent's children*)int
, (*root*)addr
, (*root parent*)addr
, (*self*)addr
) = (* view for a domtree minus a sub domtree *)
  | {n,h:nat | h <= n}
    {hf,hr,hs:nat | hs <= h; h==max(hf,max(hs,hr))+1}
    {nf,nr:nat} {lf,lmp,lm,lmn,lr:addr}
    {slfp,slfn,slfc:addr}
    {pnt:addr} {dir:nat} {rt,rtp:addr}
    {slf:agz;slfp,slfn:addr}
    DIFFnode (n, hs, lm, lmp, lmn, nf, rt, rtp, slf) of (
    // node: parent, prev, next, children, self pointers
      domnode_v (h, pnt, slfp, slfn, lf, slf)
    // siblings to the left of [lm] (following prev pointers)
    , domdlrseg_v (nf, hf, lf, null, lmp, lm, slf)
    // siblings to the right of [slf] (following next pointers)
    , domdlfseg_v (nr, hr, lmn, lm, lr, null, slf)
    // path upwards to the root
    , domdiff_v (n, h, slf, slfp, slfn, dir, rt, rtp, pnt)
    ) // end of [DIFFnode]
  | {h:nat} {chld:addr} {dir:nat} {slf:addr}
    DIFFemp (h, h, chld, null, null, dir, chld, slf, slf) of ()
// end of [domdiff_v]

// domdiff_v is essentially the current state of traversal
// of the DOM tree: DIFFnode is the "hole", or the parent of the focussed/selected
// node of the tree

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
  {chld,chldp,chldn:addr}
  {dir:nat} {rt,rtp,slf:addr} .<n-h>. (
    fpf: domdiff_v (n, h, chld, chldp, chldn, dir, rt, rtp, slf)
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
  {n,h:int} {chld,chldp,chldn:addr} {dir:int} {rt,rtp:addr}
  {slf:addr | slf <> rtp} .< >. (
    pf: domdiff_v (n, h, chld, chldp, chldn, dir, rt, rtp, slf)
  ) :<> [h0:int;pnt,slfp,slfn,lc:addr] (
    domnode_v (h0, pnt, slfp, slfn, lc, slf)
  , domnode_v (h0, pnt, slfp, slfn, lc, slf)
      -<lin,prf> domdiff_v (n, h, chld, chldp, chldn, dir, rt, rtp, slf)
  ) = let
      prval DIFFnode (pf_at, pfr, pff, fpf) = pf
    in
      #[.. | (pf_at, llam (pf_at) => DIFFnode (pf_at, pfr, pff, fpf))]
    end // end of [domdiff_takeout]

// NOTE on navigation...
// - we must ALWAYS maintain child pointer to be the current pointer
//   (so, when navigating the tree, we will be MUTATING it too)
// - how to get rid of the above restriction?
//   - only store the first child, or last child pointer?
//   - but what is first/last child? and how will we reconstruct the proof?
// - done! we will always store the first child pointer in the tree node,
//   and while navigating, we will NOT mutate anything

// the type of a rooted tree
viewdef domtree_v_root (h:int, l:addr) = domtree_v (h, null, l, null, null)

// ------------------------

// the indices we use need adjustment!
// - we don't want to traverse an empty tree, and don't want to point to a NULL node
//   - really? yes! a NULL node is not of interest at all, I guess...
//   - done, mostly
// - we would like to know when transition is illegal (later on we could simply raise exceptions
//   to considerably simplify typing for the end-user)
//   - has parent...
//   - we need separate tests to figure out if transition is valid (has_parent, has_next, has_prev...)
//   - has previous sibling: index > 0
//   - has next sibling: ???
//     - new index (for total nr of children of node), then index <= total
// - remove rtp index (I have no idea why HX needed it at all...)
// - we need to get the current node of the traversal (or better, a "map" functional:
//    it would apply some changes to the focussed node)
//    - based on that, we can supply a "clone" function
// - when moving between siblings, we want to ensure that height doesn't change much
// - better naming?
//   - domctx_vt? domzipper_vt? domnav_vt?
// what about these indices?
// - tree height, child height, nextCnt(aka nf), prevCnt(aka nr), root, self, child
//   - we can also use the current formulation: index of child, total nr of siblings
//   - root is only needed to show the tree wasn't modified during navigation
//   - what about children of child? to ensure we can navigate downwards
//   - we can also bring back rtp (parent of root), to be able to "branch off"
//     queries from the currently focussed node (e.g. for cloning focussed node)
absvt@ype domtraversal_vt (
  int(*tree height*)
, int(*missing subtree height*)
, int(*index of subtree among parent's children*)
, addr(*root*)
, addr(*parent of root*)
, addr(*parent of missing subtree*)
, addr(*missing subtree*)
) = @{p_rtp= ptr, p_root= ptr, p_slf= ptr, p_chld= ptr}
vtypedef domtraversal_vt0 =
  domtraversal_vt (0, 0, 0, null, null, null, null)?

// begin traversal (during which you retain the parent and the focussed child pointers...
// but you may also want to retain the root pointer too!
extern
fun
domtree_traversal_beg {h:nat} {rt:agz} (
  domtree_v_root (h, rt)
| p: ptr rt
, tr: &domtraversal_vt0 >> domtraversal_vt (h, h, 0, rt, null, slf, chld)
): #[slf,chld:addr | chld > null] void
// end traversal: how? given domtraversal_v, give back the proof of domtree_v_root
// - we have to maintain the root pointer somewhere
// - we do not want to burden the user with root ptr maintenance!
extern
fun
domtree_traversal_end {n,h:nat | h <= n} {dir:int} {slf,chld,rt:addr} (
  &domtraversal_vt (n, h, dir, rt, null, slf, chld) >> domtraversal_vt0
): (
  domtree_v_root (n, rt)
| ptr rt
) (* end of [domtree_traversal_end] *)
//
// moves to the first child of the focussed node
extern
fun
// pre: there exists a child!
domtree_traversal_child {n,h,dir:int} {rt,rtp,slf:addr;chld:addr} (
  &domtraversal_vt (n, h, dir, rt, rtp, slf, chld)
    >> domtraversal_vt (n, h1, 0, rt, rtp, chld, chld1)
): #[chld1:addr] #[h1:nat | h1 <= h] void
//
// moves up to the parent node
extern
fun
domtree_traversal_parent {n,h,dir:int} {rt,rtp,slf,chld:addr | slf <> rtp} (
  &domtraversal_vt (n, h, dir, rt, rtp, slf, chld)
    >> domtraversal_vt (n, h1, dir1, rt, rtp, slf1, slf)
): #[dir1,h1:nat | h <= h1; h1 <= n] #[slf1:addr] void
// checks if the focussed node has a parent
extern
fun
domtree_traversal_has_parent {n,h,dir:int} {rt,rtp,slf,chld:addr} (
  &domtraversal_vt (n, h, dir, rt, rtp, slf, chld)
): bool (slf <> rtp)
//
// moves to the following sibling
extern
fun
domtree_traversal_next {n,h,dir:int} {rt,rtp,slf,chld:addr | slf <> rtp} (
  &domtraversal_vt (n, h, dir, rt, rtp, slf, chld)
    >> domtraversal_vt (n, h1, dir+1, rt, rtp, slf, chld1)
): #[h1:nat | h1 <= n] #[chld1:addr] void
// moves to the preceding sibling
extern
fun
domtree_traversal_prev {n,h,dir:int} {rt,rtp,slf,chld:addr | slf <> rtp} (
  &domtraversal_vt (n, h, dir, rt, rtp, slf, chld)
    >> domtraversal_vt (n, h1, dir-1, rt, rtp, slf, chld1)
): #[h1:nat | h1 <= n; dir-1 >= 0] #[chld1:addr] void
//
(* ****** ****** *)
//
local
//
dataview param_validity (int, int, int, addr) =
  {n,h:nat | h <= n} {dir:nat} {chld:agz}
  param_validity_v (n, h, dir, chld)
//
assume domtraversal_vt (n:int, h:int, dir:int, rt:addr, rtp:addr, slf:addr, chld:addr) = @{
  p_rtp= ptr rtp
, p_root= ptr rt
, p_slf= ptr slf
, p_chld= ptr chld
, pf_valid = param_validity (n, h, dir, chld)
, pf_ctx = [chldp,chldn:addr] (
    domdiff_v (n, h, chld, chldp, chldn, dir, rt, rtp, slf)
  , domtree_v (h, slf, chld, chldp, chldn)
  )
} (* end of [domtraversal_vt] *)
//
in // in of [local]
//
implement
domtree_traversal_beg {h} {rt} (
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
end // end of [domtree_traversal_beg]
//
implement
domtree_traversal_end {n,h} {dir} {slf,chld,rt} (
  tr
) = let
  prval param_validity_v () = tr.pf_valid
  prval (pf_diff, pf_dom) = tr.pf_ctx
  val p_root = tr.p_root
  prval pf_tree = domdiff_domtree_join (pf_diff, pf_dom)
in
  (pf_tree | p_root)
end // end of [domtree_traversal_end]
//
implement
domtree_traversal_child {n,h,dir} {rt,rtp,slf,chld} (tr) = {
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
val () = assert (p_chld1 > the_null_ptr)
// NOTE: we can't construct a DIFFnode without a proof of domnode_v,
// and there can be NO proof of domnode_v for a null pointer
//
prval pf_rseg = domdlrseg_v_nil ()
prval domdlfseg_v_cons (pf1_tree, pf_fseg) = pf_seg
prval pf1_diff = DIFFnode (pf_at, pf_rseg, pf_fseg, pf_diff)
prval () = $effmask_wrt (tr.pf_valid := param_validity_v ())
prval () = $effmask_wrt (tr.pf_ctx := (pf1_diff, pf1_tree))
//
} (* end of [domtree_traversal_child] *)
//
implement
domtree_traversal_has_parent {n,h,dir} {rt,rtp,slf,chld} (tr) = let
//
prval param_validity_v () = tr.pf_valid
//
val res = tr.p_slf <> tr.p_rtp
//
prval () = $effmask_wrt (tr.pf_valid := param_validity_v ())
//
in
  res
end // end of [domtree_traversal_has_parent]
//
implement
domtree_traversal_parent {n,h,dir} {rt,rtp,slf,chld} (tr) = {
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
} (* end of [domtree_traversal_parent] *)
//
implement
domtree_traversal_next {n,h,dir} {rt,rtp,slf,chld} (tr) = {
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
val () = assert (p_chld1 > the_null_ptr) // FIXME
//
prval pf1_rseg = domdlrseg_v_cons (pf1_rseg, pf_tree)
prval domdlfseg_v_cons (pf1_tree, pf1_fseg) = pf1_fseg
//
prval pf2_diff = DIFFnode (pf1_at, pf1_rseg, pf1_fseg, pf1_diff)
//
prval () = $effmask_wrt (tr.pf_valid := param_validity_v ())
prval () = $effmask_wrt (tr.pf_ctx := (pf2_diff, pf1_tree))
//
} (* end of [domtree_traversal_next] *)
//
implement
domtree_traversal_prev {n,h,dir} {rt,rtp,slf,chld} (tr) = {
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
val () = assert (p_chld1 > the_null_ptr) // FIXME
//
prval domdlrseg_v_cons (pf1_rseg, pf1_tree) = pf1_rseg
prval pf1_fseg = domdlfseg_v_cons (pf_tree, pf1_fseg)
//
prval pf2_diff = DIFFnode (pf1_at, pf1_rseg, pf1_fseg, pf1_diff)
//
prval () = $effmask_wrt (tr.pf_valid := param_validity_v ())
prval () = $effmask_wrt (tr.pf_ctx := (pf2_diff, pf1_tree))
//
} (* end of [domtree_traversal_prev] *)

end // end of [local]

// what to do now?
// 1. write basic navigation functions (e.g. move to first child, move to next/prev sibling)
//    - we still might have to amend our definitions once more, to support the next/prev pointers
//      - done! i think i got definitions right...
//    - almost done!
// 2. write the split function, which finds the node by predicate,
//    splitting it along the way (based on pavltree_split)
//    - what about *many* results? this is kind of like a doubly-linked
//      list of nodes that point back into the tree nodes
//      that satisfy the predicate (a "front" through the tree)
// 3. write DOM manipulation functions from minimal DOM
//    - appendChild
//    - removeChild
//    - createNode
//    - createTextNode
//    - getChildNodes (this does a split! so you get the cake and eat it too)
// 4. wire it up to JS and try to do some real stuff

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