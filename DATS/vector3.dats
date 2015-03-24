#define ATS_PACKNAME "PLAYGROUND.vector3"
#define ATS_DYNLOADFLAG 0

#include
"share/atspre_staload.hats"

staload _ = "prelude/DATS/gnumber.dats"

staload "../SATS/vector3.sats"

#include "./SHARE/vector.hats"

// client defines constructors and destructors (vector projections)
// shared code: basically everything else

implement
vector_init (v, x, y, z) = {
//
fun
aux (v: &(@[INV(T)][NDIM])? >> _, x: T, y: T, z: T): void = {
//
prval pf_arr = view@(v)
var pv = addr@(v)
//
prval (pf1_at, pf1_arr) = array_v_uncons {T?} (pf_arr)
val () = ptr_set<T> (pf1_at | pv, x)
//
val () = pv := ptr1_succ<T> (pv)
prval (pf2_at, pf2_arr) = array_v_uncons {T?} (pf1_arr)
val () = ptr_set<T> (pf2_at | pv, y)
//
val () = pv := ptr1_succ<T> (pv)
prval (pf3_at, pf3_arr) = array_v_uncons {T?} (pf2_arr)
val () = ptr_set<T> (pf3_at | pv, z)
//
#define :: array_v_cons
//
prval pf3_nil = array_v_unnil_nil (pf3_arr)
prval () = view@(v) := pf1_at :: pf2_at :: pf3_at :: pf3_nil
//
} (* end of [aux] *)
//
val () = aux (v.V, x, y, z)
//
} (* end of [vector_init] *)

extern
fun
crossprod_vector_vector (x: &vec, y: &vec): vec

implement
crossprod_vector_vector (x, y) = res where {
//
fun
aux (v: &(@[INV(T)][NDIM])? >> _, v1: &vec, v2: &vec): void = {
//
prval pf_arr = view@(v)
var pv = addr@(v)
//
prval (pf1_at, pf1_arr) = array_v_uncons {T?} (pf_arr)
val vx = gsub_val_val<T> (gmul_val_val<T> (v1.V.[1], v2.V.[2]), gmul_val_val<T> (v1.V.[2], v2.V.[1]))
val () = ptr_set<T> (pf1_at | pv, vx)
//
val () = pv := ptr1_succ<T> (pv)
prval (pf2_at, pf2_arr) = array_v_uncons {T?} (pf1_arr)
val vy = gsub_val_val<T> (gmul_val_val<T> (v1.V.[2], v2.V.[0]), gmul_val_val<T> (v1.V.[0], v2.V.[2]))
val () = ptr_set<T> (pf2_at | pv, vy)
//
val () = pv := ptr1_succ<T> (pv)
prval (pf3_at, pf3_arr) = array_v_uncons {T?} (pf2_arr)
val vz = gsub_val_val<T> (gmul_val_val<T> (v1.V.[0], v2.V.[1]), gmul_val_val<T> (v1.V.[1], v2.V.[0]))
val () = ptr_set<T> (pf3_at | pv, vz)
//
#define :: array_v_cons
//
prval pf3_nil = array_v_unnil_nil (pf3_arr)
prval () = view@(v) := pf1_at :: pf2_at :: pf3_at :: pf3_nil
//
} (* end of [aux] *)
//
var res: vec
val () = aux (res.V, x, y)
//
} // end of [crossprod_vector_vector]


// for 3d vectors:
// - cross prod
// - ?
// for all vectors:
// - operator overloads

implement
main0 () = let
var v1: vec and v2: vec and v3: vec
val () = vector_init (v1, 1.0f, 0.0f, 0.0f)
val () = vector_init (v2, 0.0f, 1.0f, 0.0f)
val () = v3 := add_vector_vector (v1, v2)
//
val () = println!("x = ", v3.V.[0])
val () = println!("y = ", v3.V.[1])
val () = println!("z = ", v3.V.[2])
//
in
end