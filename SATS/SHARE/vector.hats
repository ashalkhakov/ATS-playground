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

fun
vector_init_clo {v:view} (
  pfv: !v
| vec: &vec? >> _
, f: &(!v | natLt(NDIM)) -<clo1> T
): void // end of [vector_init_clo]
//
fun{a:t@ype}
vector_fold_clo {v:view} (
  pfv: !v
| f: &(!v | &a >> a, natLt(NDIM)) -<clo1> void
, res: &a >> a
): void // end of [vector_fold_clo]

(* ****** ****** *)
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
dotprod_vector_vector (&vec, &vec): T
//
fun
compare_vector_vector_T (&vec, &vec, T(*epsilon*)): int
//
(* ****** ****** *)
