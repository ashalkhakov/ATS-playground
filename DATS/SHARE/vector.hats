//
extern
fun
vector_init_clo {v:view} (
  pfv: !v
| vec: &vec? >> _
, f: &(!v | natLt(NDIM)) -<clo1> T
): void // end of [vector_init_clo]
//
extern
fun{vt:vt@ype}
vector_init$fwork (natLt(NDIM), &(vt)): T
//
extern
fun{vt:vt@ype}
vector_init_env (
  vec: &vec? >> _, env: &(vt)
): void // end of [vector_init_env]
//
extern
fun{a:t@ype}
vector_fold_clo {v:view} (
  pfv: !v
| f: &(!v | &a >> a, natLt(NDIM)) -<clo1> void
, res: &a >> a
): void // end of [vector_fold_clo]
//
(* ****** ****** *)
//
extern
fun
add_vector_vector (&vec, &vec): vec
//
extern
fun
mul_T_vector (T, &vec): vec
//
extern
fun
neg_vector (&vec): vec
//
extern
fun
sub_vector_vector (&vec, &vec): vec
//
extern
fun
length_sq_vector (&vec): T
//
extern
fun
length_vector (&vec): T
//
extern
fun
dotprod_vector_vector (&vec, &vec): T
//
(*
extern
fun{}
equal_vector$eps (): T
*)
extern
fun
equal_vector_vector (&vec, &vec): bool
//
extern
fun
fprint_vector (FILEref, &vec): void
//
extern
fun
print_vector (&vec): void
//
(* ****** ****** *)
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
implement{vt}
vector_init_env (v, env) = {
//
fun
loop {i:nat | i <= NDIM} (
  res: &(@[INV(T)][NDIM-i]?) >> _, env: &vt, i: int i
) : void =
if i < NDIM then {
  val pres = addr@(res)
  prval (pfres_at, pfres_arr1) = array_v_uncons (view@(res))
  val () = !pres := vector_init$fwork<vt> (i, env)
  val (pfres_arr1 | pres_1) = viewptr_match (pfres_arr1 | ptr1_succ<T> (pres))
  val () = loop (!pres_1, env, i+1)
  prval () = view@(res) := array_v_cons (pfres_at, pfres_arr1)
} else {
  prval () = view@(res) := array_v_unnil_nil (view@(res))
} (* end of [loop] *)
//
val () = loop (v.V, env, 0)
//
} (* end of [vector_init_env] *)
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
(*
// NOTE: this doesn't work (template is not found)
implement
add_vector_vector (x, y) = let
  var res: vec
  prval [lx:addr] EQADDR () = eqaddr_make_ptr (addr@(x))
  prval [ly:addr] EQADDR () = eqaddr_make_ptr (addr@(y))
  // NOTE: the presence of variables in [VT] is what
  // makes Postiats unable to locate the template
  // for vector_init$fwork<VT>
  vtypedef VT = @(vec @ lx, vec @ ly | ptr (*lx*), ptr (*ly*))
  //
  implement
  vector_init$fwork<VT> (i, env) =
    gnumber_int<T> (0)
//    gadd_val_val<T> (x.V.[i], y.V.[i])
  //
  var env : VT = (view@(x), view@(y) | addr@(x), addr@(y))
  val () = vector_init_env<VT> (res, env)
  prval () = view@(x) := env.0
  and () = view@(y) := env.1
in
  res
end // end of [add_vector_vector]
*)
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
//
implement
length_sq_vector (x) = let
  prval pfv = view@(x)
  prval [lx:addr] EQADDR () = eqaddr_make_ptr (addr@(x))
  viewdef V = vec @ lx
  var f = lam@ (pf: !V >> _ | e: &T >> T, i: natLt(NDIM)): void => let
    val v = x.V.[i] in
    e := gadd_val_val<T> (e, gmul_val_val<T> (v, v))
  end // end of [f]
  var res: T = gnumber_int<T> (0)
  val () = vector_fold_clo<T> {V} (pfv | f, res)
  prval () = view@(x) := pfv
in
  res
end // end of [length_sq_vector]
//
implement
length_vector (x) = let
  val len_sq = length_sq_vector (x)
in
  sqrt<T> (len_sq)
end // end of [length_vector]
//
implement
dotprod_vector_vector (x, y) = let
  prval pfv = (view@(x), view@(y))
  prval [lx:addr] EQADDR () = eqaddr_make_ptr (addr@(x))
  prval [ly:addr] EQADDR () = eqaddr_make_ptr (addr@(y))
  viewdef V = (vec @ lx, vec @ ly)
  var f = lam@ (pf: !V >> _ | e: &T >> T, i: natLt(NDIM)): void =>
    e := gadd_val_val<T> (e, gmul_val_val<T> (x.V.[i], y.V.[i]))
  // end of [f]
  var res: T = gnumber_int<T> (0)
  val () = vector_fold_clo<T> {V} (pfv | f, res)
  prval () = view@(x) := pfv.0
  and () = view@(y) := pfv.1
in
  res
end // end of [dotprod_vector_vector]
//
implement
equal_vector_vector (x, y) = let
//
val eps = equal_vector$eps<> ()
//
implement
array_foreach2$cont<T,T><bool> (x0, y0, res) = let
  val d = gabs_val<T> (gsub_val_val<T> (x0, y0))
  val sgn0 = gcompare_val_val<T> (d, eps)
in
  if sgn0 < 0 then true
  else (res := false; false)
end // end of [array_foreach2$cont]
//
implement
array_foreach2$fwork<T,T><bool> (x0, y0, sgn) = ()
//
var res: bool = true
val _ = array_foreach2_env<T,T><bool> (x.V, y.V, (i2sz)NDIM, res)
//
in
//
res
//
end // end of [equal_vector_vector]

implement
fprint_vector (out, v) = {
//
implement
fprint_array$sep<> (out) = fprint (out, " ")
//
val () = fprint (out, "(")
val () = fprint_array_int<T> (out, v.V, NDIM)
val () = fprint (out, ")")
//
} (* end of [fprint_vector] *)

implement
print_vector (v) = fprint_vector (stdout_ref, v)

(* ****** ****** *)
