//
implement
vector_init_clo {v} (pfv | res, f) = {
//
fun
loop {v:view} {i:nat | i <= NDIM} (
  pfv: !v
| res: &(@[INV(T)][NDIM-i]?) >> _, f: &(!v | natLt(NDIM)) -<clo1> T, i: int i
) : void =
if i < NDIM then {
  val pres = addr@(res)
  prval (pfres_at, pfres_arr1) = array_v_uncons (view@(res))
  val () = !pres := f (pfv | i)
  val (pfres_arr1 | pres_1) = viewptr_match (pfres_arr1 | ptr1_succ<T> (pres))
  val () = loop (pfv | !pres_1, f, i+1)
  prval () = view@(res) := array_v_cons (pfres_at, pfres_arr1)
} else {
  prval () = view@(res) := array_v_unnil_nil (view@(res))
} (* end of [loop] *)
//
val () = loop (pfv | res.V, f, 0)
//
} (* end of [vector_init_clo] *)
//
implement{a}
vector_fold_clo {v} (pfv | f, x) = {
//
fun
loop {i:nat | i <= NDIM} (
  pfv: !v
| f: &(!v | &a >> a, natLt(NDIM)) -<clo1> void
, x: &a >> a, i: int i
) : void = if i < NDIM then {
  val () = f (pfv | x, i)
  val () = loop (pfv | f, x, i+1)
} // end of [loop]
//
val () = loop (pfv | f, x, 0)
} (* end of [vector_fold_clo] *)

(* ****** ****** *)

implement
add_vector_vector (x, y) = let
  var res: vec
  prval pfv = (view@(x), view@(y))
  prval [lx:addr] EQADDR () = eqaddr_make_ptr (addr@(x))
  prval [ly:addr] EQADDR () = eqaddr_make_ptr (addr@(y))
  viewdef V = (vec @ lx, vec @ ly)
  var f = lam@ (pf: !V >> _ | i: natLt(NDIM)): T =>
    gadd_val_val<T> (x.V.[i], y.V.[i])
  // end of [f]
  val () = vector_init_clo {V} (pfv | res, f)
  prval () = view@(x) := pfv.0
  and () = view@(y) := pfv.1
in
  res
end // end of [add_vector_vector]
//
implement
mul_T_vector (x, y) = let
  var res: vec
  prval pfv = (view@(y))
  prval [ly:addr] EQADDR () = eqaddr_make_ptr (addr@(y))
  viewdef V = (vec @ ly)
  var f = lam@ (pf: !V >> _ | i: natLt(NDIM)): T =>
    gmul_val_val<T> (x, y.V.[i])
  // end of [f]
  val () = vector_init_clo {V} (pfv | res, f)
  prval () = view@(y) := pfv
in
  res
end // end of [mul_T_vector]
//
implement
neg_vector (x) = let
  var res: vec
  prval pfv = (view@(x))
  prval [lx:addr] EQADDR () = eqaddr_make_ptr (addr@(x))
  viewdef V = (vec @ lx)
  var f = lam@ (pf: !V >> _ | i: natLt(NDIM)): T =>
    gneg_val<T> (x.V.[i])
  // end of [f]
  val () = vector_init_clo {V} (pfv | res, f)
  prval () = view@(x) := pfv
in
  res
end // end of [neg_vector]
//
implement
sub_vector_vector (x, y) = let
  var res: vec
  prval pfv = (view@(x), view@(y))
  prval [lx:addr] EQADDR () = eqaddr_make_ptr (addr@(x))
  prval [ly:addr] EQADDR () = eqaddr_make_ptr (addr@(y))
  viewdef V = (vec @ lx, vec @ ly)
  var f = lam@ (pf: !V >> _ | i: natLt(NDIM)): T =>
    gsub_val_val<T> (x.V.[i], y.V.[i])
  // end of [f]
  val () = vector_init_clo {V} (pfv | res, f)
  prval () = view@(x) := pfv.0
  and () = view@(y) := pfv.1
in
  res
end // end of [sub_vector_vector]

implement
dotprod_vector_vector (x, y) = let
  prval pfv = (view@(x), view@(y))
  prval [lx:addr] EQADDR () = eqaddr_make_ptr (addr@(x))
  prval [ly:addr] EQADDR () = eqaddr_make_ptr (addr@(y))
  viewdef V = (vec @ lx, vec @ ly)
  var f = lam@ (pf: !V >> _ | e: &T >> T, i: natLt(NDIM)): void =>
    e := gadd_val_val<T> (e, gmul_val_val<T> (x.V.[i], y.V.[i]))
  // end of [f]
  var res: T = gnumber_double<T> (0.0)
  val () = vector_fold_clo<T> {V} (pfv | f, res)
  prval () = view@(x) := pfv.0
  and () = view@(y) := pfv.1
in
  res
end // end of [dotprod_vector_vector]

(*
// need additions to [gnumber.sats]!
// fun{a:t0p} gcompare_val_val (a, a):<> int
// fun{a:t0p} gzero_val ():<> a
implement
compare_vector_vector_T (x, y, eps) = let
  prval pfv = (view@(x), view@(y))
  prval [lx:addr] EQADDR () = eqaddr_make_ptr (addr@(x))
  prval [ly:addr] EQADDR () = eqaddr_make_ptr (addr@(y))
  viewdef V = (vec @ lx, vec @ ly)
  var f = lam@ (pf: !V >> _ | e: int, i: natLt(NDIM)): int =>
    // ~1, 0, 1
    if
    gadd_val_val<T> (e, gmul_val_val<T> (x.V.[i], y.V.[i]))
  // end of [f]
  val res = vector_fold_clo<int> {V} (pfv | f, 0)
  prval () = view@(x) := pfv.0
  and () = view@(y) := pfv.1
in
  res
end // end of [compare_vector_vector_T]
*)

(* ****** ****** *)
