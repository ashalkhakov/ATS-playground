#define ATS_PACKNAME "PLAYGROUND.vector"
#define ATS_DYNLOADFLAG 0

#include
"share/atspre_staload.hats"

staload "../SATS/vector.sats"

(* ****** ****** *)

staload VEC2F = {
//
staload "../SATS/vector.sats"

staload _ = "prelude/DATS/gnumber.dats"
staload _ = "prelude/DATS/SHARE/gnumber_float.dats"
staload _ = "prelude/DATS/gorder.dats"

staload "libc/SATS/math.sats" // NOTE: requires -lm during compilation (for length_vector)
staload _ = "libc/DATS/math.dats"
//
typedef T = float
#define NDIM 2
typedef vec = vec2f

implement{}
equal_vec2f$eps () = 0.001f
fun{}
equal_vector$eps (): T = equal_vec2f$eps<> ()

#include "./SHARE/vector.hats"

//

implement
add_vec2f_vec2f (x, y) = add_vector_vector (x, y)
implement
mul_float_vec2f (x, y) = mul_T_vector (x, y)
implement
neg_vec2f (x) = neg_vector (x)
implement
sub_vec2f_vec2f (x, y) = sub_vector_vector (x, y)
implement
length_sq_vec2f (x) = length_sq_vector (x)
implement
length_vec2f (x) = length_vector (x)
implement
dotprod_vec2f_vec2f (x, y) = dotprod_vector_vector (x, y)
implement
equal_vec2f_vec2f (x, y) = equal_vector_vector (x, y)
implement
fprint_vec2f (x, y) = fprint_vector (x, y)
implement
print_vec2f (x) = print_vector (x)
//
//
implement
vec2f_init (v, x, y) = {
//
fun
aux (v: &(@[INV(T)][NDIM])? >> _, x: T, y: T): void = {
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
#define :: array_v_cons
//
prval pf2_nil = array_v_unnil_nil (pf2_arr)
prval () = view@(v) := pf1_at :: pf2_at :: pf2_nil
//
} (* end of [aux] *)
//
val () = aux (v.V, x, y)
//
} (* end of [vec2f_init] *)

implement
vec2f_get_x (v) = v.V.[0]
implement
vec2f_get_y (v) = v.V.[1]

implement
vec2f_set_x (v, x) = v.V.[0] := x
implement
vec2f_set_y (v, y) = v.V.[1] := y

} // end of [staload]

(* ****** ****** *)

staload VEC3F = {
//
staload "../SATS/vector.sats"

staload _ = "prelude/DATS/gnumber.dats"
staload _ = "prelude/DATS/SHARE/gnumber_float.dats"
staload _ = "prelude/DATS/gorder.dats"

staload "libc/SATS/math.sats" // NOTE: requires -lm during compilation (for length_vector)
staload _ = "libc/DATS/math.dats"
//
typedef T = float
#define NDIM 3
typedef vec = vec3f

implement{}
equal_vec3f$eps () = 0.001f
fun{}
equal_vector$eps (): T = equal_vec3f$eps<> ()

#include "./SHARE/vector.hats"

implement
add_vec3f_vec3f (x, y) = add_vector_vector (x, y)
implement
mul_float_vec3f (x, y) = mul_T_vector (x, y)
implement
neg_vec3f (x) = neg_vector (x)
implement
sub_vec3f_vec3f (x, y) = sub_vector_vector (x, y)
implement
length_sq_vec3f (x) = length_sq_vector (x)
implement
length_vec3f (x) = length_vector (x)
implement
dotprod_vec3f_vec3f (x, y) = dotprod_vector_vector (x, y)
implement
equal_vec3f_vec3f (x, y) = equal_vector_vector (x, y)
implement
fprint_vec3f (x, y) = fprint_vector (x, y)
implement
print_vec3f (x) = print_vector (x)
//
//
implement
vec3f_init (v, x, y, z) = {
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
} (* end of [vec3f_init] *)

implement
crossprod_vec3f_vec3f (x, y) = res where {
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
} // end of [crossprod_vec3f_vec3f]

implement
vec3f_get_x (v) = v.V.[0]
implement
vec3f_get_y (v) = v.V.[1]
implement
vec3f_get_z (v) = v.V.[2]

implement
vec3f_set_x (v, x) = v.V.[0] := x
implement
vec3f_set_y (v, y) = v.V.[1] := y
implement
vec3f_set_z (v, z) = v.V.[2] := z

} // end of [staload]

(* ****** ****** *)

staload VEC4F = {
//
staload "../SATS/vector.sats"

staload _ = "prelude/DATS/gnumber.dats"
staload _ = "prelude/DATS/SHARE/gnumber_float.dats"
staload _ = "prelude/DATS/gorder.dats"

staload "libc/SATS/math.sats" // NOTE: requires -lm during compilation (for length_vector)
staload _ = "libc/DATS/math.dats"
//
typedef T = float
#define NDIM 4
typedef vec = vec4f

implement{}
equal_vec4f$eps () = 0.001f
fun{}
equal_vector$eps (): T = equal_vec4f$eps<> ()

#include "./SHARE/vector.hats"

implement
add_vec4f_vec4f (x, y) = add_vector_vector (x, y)
implement
mul_float_vec4f (x, y) = mul_T_vector (x, y)
implement
neg_vec4f (x) = neg_vector (x)
implement
sub_vec4f_vec4f (x, y) = sub_vector_vector (x, y)
implement
length_sq_vec4f (x) = length_sq_vector (x)
implement
length_vec4f (x) = length_vector (x)
implement
dotprod_vec4f_vec4f (x, y) = dotprod_vector_vector (x, y)
implement
equal_vec4f_vec4f (x, y) = equal_vector_vector (x, y)
implement
fprint_vec4f (x, y) = fprint_vector (x, y)
implement
print_vec4f (x) = print_vector (x)
//
//
implement
vec4f_init (v, x, y, z, w) = {
//
fun
aux (v: &(@[INV(T)][NDIM])? >> _, x: T, y: T, z: T, w: T): void = {
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
val () = pv := ptr1_succ<T> (pv)
prval (pf4_at, pf4_arr) = array_v_uncons {T?} (pf3_arr)
val () = ptr_set<T> (pf4_at | pv, w)
//
#define :: array_v_cons
//
prval pf4_nil = array_v_unnil_nil (pf4_arr)
prval () = view@(v) := pf1_at :: pf2_at :: pf3_at :: pf4_at :: pf4_nil
//
} (* end of [aux] *)
//
val () = aux (v.V, x, y, z, w)
//
} (* end of [vec4f_init] *)

implement
vec4f_get_x (v) = v.V.[0]
implement
vec4f_get_y (v) = v.V.[1]
implement
vec4f_get_z (v) = v.V.[2]
implement
vec4f_get_w (v) = v.V.[3]

implement
vec4f_set_x (v, x) = v.V.[0] := x
implement
vec4f_set_y (v, y) = v.V.[1] := y
implement
vec4f_set_z (v, z) = v.V.[2] := z
implement
vec4f_set_w (v, w) = v.V.[3] := w

} // end of [staload]

(* ****** ****** *)
fun
test_compare () = let
  var v0: vec3f
  var v1: vec3f
  var v2: vec3f
  var v3: vec3f
  val () = vec3f_init (v0, 1.0f, 0.0f, 0.0f)
  val () = vec3f_init (v1, 1.0f, 1.0f, 1.0f)
  val () = vec3f_init (v2, 0.5f, 1.0f, 0.0f)
  val () = vec3f_init (v3, 0.0f, 1.0f, 2.0f)
  
  val () = println!("test_compare BEG")
  
  val () = (print("v0 = "); print (v0); print_newline ())
  val () = (print("v1 = "); print (v1); print_newline ())
  val () = (print("v2 = "); print (v2); print_newline ())
  val () = (print("v3 = "); print (v3); print_newline ())

  implement
  equal_vec3f$eps<> () = 0.001f
  #define CMP equal_vec3f_vec3f
  
  val () = println!("v0, v0 = ", CMP (v0, v0))
  val () = println!("v0, v1 = ", CMP (v0, v1))
  val () = println!("v0, v2 = ", CMP (v0, v2))
  val () = println!("v0, v3 = ", CMP (v0, v3))
  
  val () = println!("v1, v0 = ", CMP (v1, v0))
  val () = println!("v1, v1 = ", CMP (v1, v1))
  val () = println!("v1, v2 = ", CMP (v1, v2))
  val () = println!("v1, v3 = ", CMP (v1, v3))
  
  val () = println!("v2, v0 = ", CMP (v2, v0))
  val () = println!("v2, v1 = ", CMP (v2, v1))
  val () = println!("v2, v2 = ", CMP (v2, v2))
  val () = println!("v2, v3 = ", CMP (v2, v3))
  
  val () = println!("v3, v0 = ", CMP (v3, v0))
  val () = println!("v3, v1 = ", CMP (v3, v1))
  val () = println!("v3, v2 = ", CMP (v3, v2))
  val () = println!("v3, v3 = ", CMP (v3, v3))

  val () = println!("test_compare END")
in
end

implement
main0 () = let
var v1: vec3f
var v2: vec3f
var v3: vec3f
val () = v1.init (1.0f, 0.0f, 0.0f)
val () = v2.init (0.0f, 1.0f, 0.0f)
val () = v3 := v1 + v2
//
val () = println!("x = ", v3.x())
val () = println!("y = ", v3.y())
val () = println!("z = ", v3.z())
//
val () = test_compare ()
in
end