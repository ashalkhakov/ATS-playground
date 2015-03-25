(*
abst@ype T(*scalar*)
#define NDIM 3
#define REPR_TYPE "vec3_t"

typedef
vector_t0ype =
$extype_struct REPR_TYPE of {
  V= @[T][NDIM]
}

stadef vec = vector_t0ype // local shorthand

fun
vector_init (&vector_t0ype? >> vec, T, T, T): void
*)
(* ****** ****** *)
//
fun
vector_init_clo {v:view} (
  pfv: !v
| vec: &vec? >> _
, f: &(!v | natLt(NDIM)) -<clo1> T
): void // end of [vector_init_clo]
//
fun{vt:vt@ype}
vector_init$fwork (natLt(NDIM), &(vt)): T
//
fun{vt:vt@ype}
vector_init_env (
  vec: &vec? >> _, env: &(vt)
): void // end of [vector_init_env]
//
fun{a:t@ype}
vector_fold_clo {v:view} (
  pfv: !v
| f: &(!v | &a >> a, natLt(NDIM)) -<clo1> void
, res: &a >> a
): void // end of [vector_fold_clo]
//
(* ****** ****** *)
//
// how to declare these properly?
//
typedef
vector_binop_type = (&vec, &vec) -> vec
//
typedef
vector_unop_type = (&vec) -> vec
//
typedef
vector_T_mul_type = (T, &vec) -> vec
//
typedef
vector_T_type = (&vec) -> T
//
fun
add_vector_vector (&vec, &vec): vec
//
fun
mul_T_vector (T, &vec): vec
//
fun
neg_vector (&vec): vec
//
fun
sub_vector_vector (&vec, &vec): vec
//
fun
length_sq_vector (&vec): T
//
fun
length_vector (&vec): T
//
fun
dotprod_vector_vector (&vec, &vec): T
//
// TODO: use compare_vector_vector_eps
// where eps is a function template
// (just the usual comparison function)
// - also, better supply an equality function (not general comparison!)
// - what about ordering (lt/gt)? do we even need it?
fun{}
equal_vector_vector$eps (): T
fun
equal_vector_vector (&vec, &vec): bool
//
fun
fprint_vector (FILEref, &vec): void
//
fun
print_vector (&vec): void
//
(* ****** ****** *)
