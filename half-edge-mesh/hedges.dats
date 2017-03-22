// Half-edge collapse operation (generalized
// to handle slightly-non-2-manifold surfaces).

#include "share/atspre_staload.hats"

staload UN = "prelude/SATS/unsafe.sats"

(*
 * AS-20141202: see also ATS0/proto for an idea of using
 * view containment to enforce "no dangling pointers":
 * - if you have v:view, and vcontain_p(v, a@l), then you can write to a@l
 * - this allows us to model a "heap" which is linear, but pointers inside it
 *   can alias each other just fine
 * - basically, every mesh is a heap, and all of its edges, faces, vertices
 *   are contained within it (all of those can be seen as cptr-s, C-like
 *   pointers)
 * - it certainly isn't a good idea to let the above details leak
 *   into the interface, but it's a nice implementation idea nonetheless
 * AS-20151222: it is done! and it seems to work nicely using "regions"
 * and "region pointers"
 *)

absvt@ype mesh (int, int, int, l0:addr) = @{
  verts= ptr
, nverts= size_t
, faces= ptr
, nfaces= size_t
, hedges= ptr
, nhedges= size_t
}
vtypedef mesh (l0:addr) = [nv,nf,nh:int] mesh (nv,nf,nh,l0)

abst@ype vtx (bool, addr) = ptr
typedef vtx0 (l0:addr) = [b:bool] vtx (b, l0)
typedef vtx1 (l0:addr) = vtx (true, l0)

abst@ype hedge (bool, addr) = ptr
typedef hedge0 (l0:addr) = [b:bool] hedge (b, l0)
typedef hedge1 (l0:addr) = hedge (true, l0)

abst@ype face (bool, addr) = ptr
typedef face0 (l0:addr) = [b:bool] face (b, l0)
typedef face1 (l0:addr) = face (true, l0)

(* ****** ****** *)

symintr .next .prev .twin .vtx .face
symintr .active

(* ****** ****** *)
//
extern
fun next_get: {l0:addr} (&mesh (l0), hedge1 (l0)) -> hedge1 (l0) // total
and next_set: {l0:addr} (&mesh (l0) >> mesh (l0), hedge1 (l0), hedge1 (l0)) -> void
overload .next with next_get
overload .next with next_set
//
extern
fun prev_get: {l0:addr} (&mesh (l0), hedge1 (l0)) -> hedge1 (l0) // total
and prev_set: {l0:addr} (&mesh (l0), hedge1 (l0), hedge1 (l0)) -> void
overload .prev with prev_get
overload .prev with prev_set
//
extern
fun twin_get: {l0:addr} (&mesh (l0), hedge1 (l0)) -> hedge0 (l0) // partial, may yield null
and twin_set: {l0:addr} (&mesh (l0), hedge1 (l0), hedge0 (l0)) -> void
overload .twin with twin_get
overload .twin with twin_set
//
extern
fun vtx_get: {l0:addr} (&mesh (l0), hedge1 (l0)) -> vtx1 (l0)
and vtx_set: {l0:addr} (&mesh (l0), hedge1 (l0), vtx1 (l0)) -> void
overload .vtx with vtx_get
overload .vtx with vtx_set
//
extern
fun face_get: {l0:addr} (&mesh (l0), hedge1 (l0)) -> face1 (l0)
and face_set: {l0:addr} (&mesh (l0), hedge1 (l0), face1 (l0)) -> void
overload .face with face_get
overload .face with face_set
//
extern
fun hedge_none {l0:addr} (): hedge(false, l0)
//
extern
fun hedge_is_none: {l0:addr} {b:bool} hedge (b, l0) -> bool (~b)
and hedge_is_some: {l0:addr} {b:bool} hedge (b, l0) -> bool (b)
overload iseqz with hedge_is_none
overload isneqz with hedge_is_some
//
extern
fun eq_hedge_hedge: {l0:addr} (hedge0 (l0), hedge0 (l0)) -> bool
overload = with eq_hedge_hedge
//
extern
fun neq_hedge_hedge: {l0:addr} (hedge0 (l0), hedge0 (l0)) -> bool
overload <> with neq_hedge_hedge
//
(* ****** ****** *)
//
extern
fun face_active_get: {l0:addr} (&mesh (l0), face1 (l0)) -> bool
and face_active_set: {l0:addr} (&mesh (l0), face1 (l0), bool) -> void
overload .active with face_active_get
overload .active with face_active_set
//
(* ****** ****** *)

extern
fun eq_vtx_vtx: {l0:addr} (vtx0 (l0), vtx0 (l0)) -> bool
overload = with eq_vtx_vtx

(* ****** ****** *)
//
extern
fun collapse {l0:addr} (&mesh (l0) >> mesh (l0), h: hedge1 (l0)): void
//
extern
fun split {l0:addr} (&mesh (l0) >> mesh (l0), h: hedge1 (l0)): void
//
(* ****** ****** *)

fun edge {l0:addr} (m: &mesh (l0), h: hedge1 (l0), g: hedge1 (l0)): bool = let
  val nextg = m.next(g)
  val vnextg = m.vtx(nextg)
  val vh = m.vtx(h)
  val vg = m.vtx(g)
  val nexth = m.next(h)
  val vnexth = m.vtx(nexth)
in
  vh = vnextg && vg = vnexth
end

local

// in:
// - h starts at vertex v
// - g ends at vertex v
// out:
// - h starts at vertex a
// - g ends at vertex a
fun
loop {l0:addr} (m: &mesh (l0), a: vtx1 (l0), h: hedge0 (l0), g: hedge0 (l0)): void =
//
if hedge_is_some (h) then let
//
val () = m.vtx(h, a) // := a
//
in
//
if hedge_is_some (g) then let
  val nextg = m.next(g)
  val () = m.vtx(nextg, a)
  val prevh = m.prev(h)
in
  if ~edge (m, prevh, nextg) then let
    val prevh = m.prev(h)
    val tprevh = m.twin(prevh)
    val nextg = m.next(g)
    val tnextg = m.twin(nextg)
  in
    loop (m, a, tprevh, tnextg)
  end
end else let
  val prevh = m.prev(h)
  val tprevh = m.twin(prevh)
in
  loop (m, a, tprevh, hedge_none ())
end
//
end else begin // h is nil
//
if hedge_is_some (g) then let
  val nextg = m.next(g)
  val () = m.vtx(nextg, a)
  val tnextg = m.twin(nextg)
in
  loop (m, a, hedge_none (), tnextg)
end else ()
//
end // end of [loop]
//
in // of [local]
//
implement
collapse {l0} (m, h) = {
//
fn twinize (m: &mesh (l0) >> mesh (l0), h: hedge1 (l0), g: hedge0 (l0)): hedge0 (l0) = let
  val h = m.twin(h)
in
  if hedge_is_some (h) then begin
    m.twin(h, g);
    if hedge_is_some (g) then m.twin(g, h)
  end else begin
    if hedge_is_some (g) then m.twin(g, hedge_none ());
  end;
  g
end // end of [twinize]
//
val faceh = m.face(h)
val () = m.active(faceh, false)
val nexth = m.next(h)
val prevh = m.prev(h)
val tprevh = m.twin(prevh)
val h1 = twinize (m, nexth, tprevh)
//
val g1 = let
  val g = m.twin(h)
in
  if hedge_is_some (g) then let
    val faceg = m.face(g)
    val () = m.active (faceg, false)
    val prevg = m.prev(g)
    val nextg = m.next(g)
    val tnextg = m.twin(nextg)
  in
    twinize (m, prevg, tnextg)
  end else hedge_none ()
end // end of [val]
//
val nexth = m.next(h)
val vnexth = m.vtx(nexth)
val () = loop (m, vnexth, h1, g1)
//
} (* end of [collapse] *)

(* ****** ****** *)

implement
split {l0:addr} (m, h) = {
//
fn twinize (m: &mesh (l0) >> mesh (l0), h: hedge1 (l0)): hedge0 (l0) = let
  val g = m.twin(h)
in
  if hedge_is_some (g) then m.twin(g, h);
  g
end // end of [twinize]
//
val faceh = m.face(h)
val () = m.active(faceh, true)
val nexth = m.next(h)
val _ = twinize (m, nexth)
val prevh = m.prev(h)
val h1 = twinize (m, prevh)
//
val g1 = let
  val g = m.twin(h)
in
  if hedge_is_some (g) then let
    val faceg = m.face(g)
    val () = m.active(faceg, true)
    val prevg = m.prev(g)
    val _ = twinize (m, prevg)
    val nextg = m.next(g)
  in
    twinize (m, nextg)
  end else hedge_none ()
end // end of [val]
//
val vh = m.vtx(h)
val () = loop (m, vh, h1, g1)
//
} (* end of [split] *)
//
end // of [local]

(* ****** ****** *)
//
local
//
staload "./rgn.sats"
//
staload _ = "prelude/DATS/pointer.dats"
//
typedef
vtx_t (l0:addr) = @{
  xyz= @(int,int,int),
  face= face1 (l0)
} (* end of [vtx_t] *)
//
typedef
hedge_t (l0:addr) = @{
  vt= vtx1 (l0)
, nxt= hedge1 (l0)
, prv= hedge1 (l0)
, twn= hedge0 (l0)
, face= face1 (l0)
} (* end of [hedge_t] *)
//typedef hedge0_t = [l:addr] hedge_t (l)
//
typedef
face_t (l0:addr) = @{
  fst= hedge1 (l0)
, active= bool
} (* end of [face_t] *)
//
assume vtx (b:bool, l0:addr) = ptr // rgnptr (vtx_t, l0, b)
assume hedge (b:bool, l0:addr) = ptr // rgnptr (hedge_t, l0, b)
assume face (b:bool, l0:addr) = ptr // rgnptr (face_t, l0, b)
//
assume mesh (nv:int,nf:int,nh:int,l0:addr) = @{
  verts= arrayptr (vtx_t(l0), nv)
, nverts= size_t nv
, faces= arrayptr (face_t(l0), nf)
, nfaces= size_t nf
, hedges= arrayptr (hedge_t(l0), nh)
, nhedges= size_t nh
, pf_rgn= RGN (l0)
} (* end of [mesh] *)
//
in // in of [local]
//
staload UN = "prelude/SATS/unsafe.sats"
//
implement
next_get {l0} (m, h) = let
  val (pf_at, fpf | p_h) = $UN.ptr0_vtake {hedge_t(l0)} (h)
  val res = p_h->nxt
  prval () = fpf (pf_at)
(*  val ((pf_at, fpf) | p_h) = rgnptr_takeout (*{hedge_t}*) (m.pf_rgn | h)
  val res = p_h->nxt
  prval () = $effmask_wrt (m.pf_rgn := fpf (pf_at))*)
in
  res
end // end of [next_get]
end
implement main0 () = ()
////
//
implement
next_set {l0} (m, h, g) = {
  val (pf_at, fpf | p_h) = rgnptr_takeout {hedge_t(l0)} (m.pf_rgn | h)
  val res = !p_h.nxt := g
  prval () = $effmask_wrt (m.pf_rgn := fpf (pf_at))
} (* end of [next_set] *)
//
implement
prev_get {l0} (m, h) = let
  val (pf_at, fpf | p_h) = rgnptr_takeout {hedge_t(l0)} (m.pf_rgn | h)
  // NOTE: what about just forward-iterating over the half-edges?
  // then we don't have to store anything
  val res = !p_h.prv
  prval () = $effmask_wrt (m.pf_rgn := fpf (pf_at))
in
  res
end // end of [prev_get]
//
implement
prev_set {l0} (m, h, g) = {
  val (pf_at, fpf | p_h) = rgnptr_takeout {hedge_t(l0)} (m.pf_rgn | h)
  // NOTE: if not storing the pointer, set [m.next (m, g, h)]
  val res = !p_h.prv := g
  prval () = $effmask_wrt (m.pf_rgn := fpf (pf_at))
} (* end of [prev_set] *)
//
implement
twin_get {l0} (m, h) = let
  val (pf_at, fpf | p_h) = rgnptr_takeout {hedge_t(l0)} (m.pf_rgn | h)
  val res = !p_h.twn
  prval () = $effmask_wrt (m.pf_rgn := fpf (pf_at))
in
  res
end // end of [twin_get]
//
implement
twin_set {l0} (m, h, g) = {
  val (pf_at, fpf | p_h) = rgnptr_takeout {hedge_t(l0)} (m.pf_rgn | h)
  val res = !p_h.twn := g
  prval () = $effmask_wrt (m.pf_rgn := fpf (pf_at))
} (* end of [twin_set] *)
//
implement
vtx_get {l0} (m, h) =let
  val (pf_at, fpf | p_h) = rgnptr_takeout {hedge_t(l0)} (m.pf_rgn | h)
  val res = !p_h.vtx
  prval () = $effmask_wrt (m.pf_rgn := fpf (pf_at))
in
  res
end // end of [vtx_get]
//
implement
vtx_set {l0} (m, h, v) = {
  val (pf_at, fpf | p_h) = rgnptr_takeout {hedge_t(l0)} (m.pf_rgn | h)
  val () = !p_h.vtx := v
  prval () = $effmask_wrt (m.pf_rgn := fpf (pf_at))
} (* end of [vtx_set] *)
//
implement
face_get {l0} (m, h) = let
  val (pf_at, fpf | p_h) = rgnptr_takeout {hedge_t(l0)} (m.pf_rgn | h)
  val res = !p_h.face
  prval () = $effmask_wrt (m.pf_rgn := fpf (pf_at))
in
  res
end // end of [face_get]
//
implement
face_set {l0} (m, h, f) = {
  val (pf_at, fpf | p_h) = rgnptr_takeout {hedge_t(l0)} (m.pf_rgn | h)
  val () = !p_h.face := f
  prval () = $effmask_wrt (m.pf_rgn := fpf (pf_at))
} (* end of [face_set] *)
//
implement
hedge_none {l0} () = rgnptr_make_none {hedge_t(l0)} {l0} ()
//
implement
hedge_is_none {l0} {b} (h) = rgnptr_is_none (h)
implement
hedge_is_some {l0} {b} (h) = rgnptr_is_some (h)
//
implement
eq_hedge_hedge {l0} (h, g) = eq_rgnptr_rgnptr (h, g)
//
implement
neq_hedge_hedge {l0} (h, g) = neq_rgnptr_rgnptr (h, g)
//
implement
face_active_get {l0} (m, f) = let
  val (pf_at, fpf | p_f) = rgnptr_takeout {face_t(l0)} (m.pf_rgn | f)
  val res = !p_f.active
  prval () = $effmask_wrt (m.pf_rgn := fpf (pf_at))
in
  res
end // end of [face_active_get]
//
implement
face_active_set {l0} (m, f, a) = {
  val (pf_at, fpf | p_f) = rgnptr_takeout {face_t(l0)} (m.pf_rgn | f)
  val () = !p_f.active := a
  prval () = $effmask_wrt (m.pf_rgn := fpf (pf_at))
} (* end of [face_active_set] *)
//
implement
eq_vtx_vtx {l0} (v1, v2) = eq_rgnptr_rgnptr (v1, v2)
//
end // end of [local]

(* ****** ****** *)

(*
testing?
- need a simple manifold to test this
  - I think I have something working already on my HP625
- collapse is always the inverse of split

improvements?
- we can save the sequence of collapse operations
  to get the usual progressive meshes (or, we could
  start from the coarse-grained mesh instead, so we
  would be using a sequence of uncollapse operations)
  - (@[hedge1][N], int i), i >=0, i < N
  - array of collapses, with the current half-edge to collapse
    being given by the index i
- what metric to use for collapsing edges? what edges
  must never be collapsed?
- interactive LOD?
*)

implement
main0 () = ()
