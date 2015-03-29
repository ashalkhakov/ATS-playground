staload "./vector.sats"

// T
// NROW
// NCOL

// mat3x3f
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
identity_mat3x3f (): mat3x3f
fun
mul_vec3f_mat3x3f (&vec3f, &mat3x3f): vec3f
fun
fprint_mat3x3f (FILEref, &mat3x3f): void
fun
print_mat3x3f (&mat3x3f): void

// TODO: overloads

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

// mat4x4f
