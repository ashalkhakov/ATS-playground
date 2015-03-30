staload "./vector.sats"

// threshold of determinant when it is considered too small
// for the matrix inverse to be calculated
fun{a:t@ype}
gdet_treshold (): a

(* ****** ****** *)

%{^

#ifndef ATS_MAT3X3F_DEFINED
#define ATS_MAT3X3F_DEFINED

typedef
struct {
  vec3f_t M[3];
} mat3x3f_t;

#endif /* ATS_MAT3X3F_DEFINED */
%}

typedef
matrix_3_3_float_t0ype =
$extype_struct "mat3x3f_t" of {
  M= @[vec3f][3] // NOTE: column-vectors!
}

stadef mat3x3f = matrix_3_3_float_t0ype // local shorthand
//

// construct a matrix from a single scalar T
fun
mat3x3f_init1 (&mat3x3f? >> _, float): void

// construct a matrix from NROW*NCOL scalars T
fun
mat3x3f_init9 (
  &mat3x3f? >> _,
  s00: float, s10: float, s20: float,
  s01: float, s11: float, s21: float,
  s02: float, s12: float, s22: float
): void

// construct a matrix from NCOL vectors of NDIM=NROW
fun
mat3x3f_init3_vec3f (
  &mat3x3f? >> _,
  col0: &vec3f, col1: &vec3f, col2: &vec3f
): void

// construct a matrix from first NROW*NCOL elements of array of T
fun
mat3x3f_init_arrptr {n:nat | n >= 9} (
  &mat3x3f? >> _,
  &(@[float][n]) >> _
): void

overload .init with mat3x3f_init1
overload .init with mat3x3f_init9
overload .init with mat3x3f_init_arrptr

fun
mat3x3f_get_int_int (&mat3x3f, row: natLt(3), col: natLt(3)): float
fun
mat3x3f_get_int (&mat3x3f, i: natLt(3*3)): float
fun
mat3x3f_set_int_int (&mat3x3f, row: natLt(3), col: natLt(3), float): void
fun
mat3x3f_set_int (&mat3x3f, i:natLt(3*3), float): void

overload [] with mat3x3f_get_int_int of 10
overload [] with mat3x3f_get_int of 10
overload [] with mat3x3f_set_int_int of 10
overload [] with mat3x3f_set_int of 10

fun
add_mat3x3f_mat3x3f (&mat3x3f, &mat3x3f): mat3x3f
fun
add_float_mat3x3f (float, &mat3x3f): mat3x3f
fun
mul_float_mat3x3f (float, &mat3x3f): mat3x3f
fun
mul_mat3x3f_mat3x3f (&mat3x3f, &mat3x3f): mat3x3f
fun
sub_mat3x3f_mat3x3f (&mat3x3f, &mat3x3f): mat3x3f
fun
neg_mat3x3f (&mat3x3f): mat3x3f
fun
invert_mat3x3f (&mat3x3f): mat3x3f
fun
invert_mat3x3f_mat3x3f (&mat3x3f, &mat3x3f? >> opt (mat3x3f, b)): #[b:bool] bool b
fun
transpose_mat3x3f (&mat3x3f): mat3x3f
fun
identity_mat3x3f (&mat3x3f? >> _): void
fun
mul_vec3f_mat3x3f (&vec3f, &mat3x3f): vec3f
fun
fprint_mat3x3f (FILEref, &mat3x3f): void
fun
print_mat3x3f (&mat3x3f): void

//
overload + with add_mat3x3f_mat3x3f
overload + with add_float_mat3x3f
overload * with mul_float_mat3x3f
overload * with mul_mat3x3f_mat3x3f
overload - with sub_mat3x3f_mat3x3f
overload ~ with neg_mat3x3f
overload invert with invert_mat3x3f
overload invert with invert_mat3x3f_mat3x3f
overload transpose with transpose_mat3x3f
overload .identity with identity_mat3x3f
overload * with mul_vec3f_mat3x3f
overload fprint with fprint_mat3x3f
overload print with print_mat3x3f
//

// specifics
// - translation_of_mat (&mat3x3): vec2
// - mat_of_translation (&vec2): mat3x3
// - translation_of_mat (&mat4x4): vec3
// - mat_of_translation (&vec3): mat4x4
// - mat_of_scale (&vec2): mat3x3
// - mat_of_scale (&vec3): mat4x4
// - mat4_of_rotation3 (&mat3x3): mat4x4
// - mat3_of_rotationX (&vec2): mat3x3
// - mat3_of_rotationY (&vec2): mat3x3
// - mat3_of_rotationZ (&vec2): mat3x3
// - mat3_of_rotationX (T): mat3x3 // angle in radians
// - mat3_of_rotationY (T): mat3x3 // angle in radians
// - mat3_of_rotationZ (T): mat3x3 // angle in radians
// - mat4_of_perspective (T, T, T, T, T): mat4x4
// - mat4_of_ortho //
// - mat4_of_look_at //

(* ****** ****** *)

%{^

#ifndef ATS_MAT4X4F_DEFINED
#define ATS_MAT4X4F_DEFINED

typedef
struct {
  vec4f_t M[4];
} mat4x4f_t;

#endif /* ATS_MAT4X4F_DEFINED */
%}

typedef
matrix_4_4_float_t0ype =
$extype_struct "mat4x4f_t" of {
  M= @[vec4f][4] // NOTE: column-vectors!
}

stadef mat4x4f = matrix_4_4_float_t0ype // local shorthand
//

fun
mat4x4f_init1 (&mat4x4f? >> _, float): void
//
fun
mat4x4f_init16 (
  &mat4x4f? >> _,
  s00: float, s10: float, s20: float, s30: float,
  s01: float, s11: float, s21: float, s31: float,
  s02: float, s12: float, s22: float, s32: float,
  s03: float, s13: float, s23: float, s33: float
): void
//
fun
mat4x4f_init4_vec4f (
  &mat4x4f? >> _,
  col0: &vec4f, col1: &vec4f, col2: &vec4f, col3: &vec4f
): void
//
fun
mat4x4f_init_arrptr {n:nat | n >= 16} (
  &mat4x4f? >> _,
  &(@[float][n]) >> _
): void

overload .init with mat4x4f_init1
overload .init with mat4x4f_init16
overload .init with mat4x4f_init_arrptr

fun
mat4x4f_get_int_int (&mat4x4f, row: natLt(4), col: natLt(4)): float
fun
mat4x4f_get_int (&mat4x4f, i: natLt(4*4)): float
fun
mat4x4f_set_int_int (&mat4x4f, row: natLt(4), col: natLt(4), float): void
fun
mat4x4f_set_int (&mat4x4f, i: natLt(3*3), float): void

overload [] with mat4x4f_get_int_int of 10
overload [] with mat4x4f_get_int of 10
overload [] with mat4x4f_set_int_int of 10
overload [] with mat4x4f_set_int of 10

fun
add_mat4x4f_mat4x4f (&mat4x4f, &mat4x4f): mat4x4f
fun
add_float_mat4x4f (float, &mat4x4f): mat4x4f
fun
mul_float_mat4x4f (float, &mat4x4f): mat4x4f
fun
mul_mat4x4f_mat4x4f (&mat4x4f, &mat4x4f): mat4x4f
fun
sub_mat4x4f_mat4x4f (&mat4x4f, &mat4x4f): mat4x4f
fun
neg_mat4x4f (&mat4x4f): mat4x4f
fun
invert_mat4x4f (&mat4x4f): mat4x4f
fun
invert_mat4x4f_mat4x4f (&mat4x4f, &mat4x4f? >> opt (mat4x4f, b)): #[b:bool] bool b
fun
transpose_mat4x4f (&mat4x4f): mat4x4f
fun
identity_mat4x4f (&mat4x4f? >> _): void
fun
mul_vec4f_mat4x4f (&vec4f, &mat4x4f): vec4f
fun
fprint_mat4x4f (FILEref, &mat4x4f): void
fun
print_mat4x4f (&mat4x4f): void

//
overload + with add_mat4x4f_mat4x4f
overload + with add_float_mat4x4f
overload * with mul_float_mat4x4f
overload * with mul_mat4x4f_mat4x4f
overload - with sub_mat4x4f_mat4x4f
overload ~ with neg_mat4x4f
overload invert with invert_mat4x4f
overload invert with invert_mat4x4f_mat4x4f
overload transpose with transpose_mat4x4f
overload .identity with identity_mat4x4f
overload * with mul_vec4f_mat4x4f
overload fprint with fprint_mat4x4f
overload print with print_mat4x4f
//
