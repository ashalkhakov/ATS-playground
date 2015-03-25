#define ATS_PACKNAME "PLAYGROUND.vector3"

(* ****** ****** *)

%{^

#ifndef ATS_VEC2F_DEFINED
#define ATS_VEC2F_DEFINED

typedef
struct {
  float V[2];
} vec2f_t;

#endif /* ATS_VEC2F_DEFINED */

%}

typedef
vector_2_float_t0ype =
$extype_struct "vec2f_t" of {
  V= @[float][2]
}

stadef vec2f = vector_2_float_t0ype // local shorthand

fun add_vec2f_vec2f (&vec2f, &vec2f): vec2f
fun mul_float_vec2f (float, &vec2f): vec2f
fun neg_vec2f (&vec2f): vec2f
fun sub_vec2f_vec2f (&vec2f, &vec2f): vec2f
fun length_sq_vec2f (&vec2f): float
fun length_vec2f (&vec2f): float
fun dotprod_vec2f_vec2f (&vec2f, &vec2f): float
fun{}
equal_vec2f$eps (): float
fun
equal_vec2f_vec2f (&vec2f, &vec2f): bool
fun
fprint_vec2f (FILEref, &vec2f): void
fun
print_vec2f (&vec2f): void

//
overload + with add_vec2f_vec2f
overload * with mul_float_vec2f
overload ~ with neg_vec2f
overload - with sub_vec2f_vec2f
overload .length_sq with length_sq_vec2f
overload .length with length_vec2f
overload dotprod with dotprod_vec2f_vec2f
overload = with equal_vec2f_vec2f
overload fprint with fprint_vec2f
overload print with print_vec2f
//

fun
vec2f_init (&vec2f? >> _, float, float): void
overload .init with vec2f_init

fun
vec2f_get_x (&vec2f): float
fun
vec2f_get_y (&vec2f): float

overload .x with vec2f_get_x
overload .y with vec2f_get_y

fun
vec2f_set_x (&vec2f, float): void
fun
vec2f_set_y (&vec2f, float): void

overload .x with vec2f_set_x
overload .y with vec2f_set_y

(* ****** ****** *)

%{^

#ifndef ATS_VEC3F_DEFINED
#define ATS_VEC3F_DEFINED

typedef
struct {
  float V[3];
} vec3f_t;

#endif /* ATS_VEC3F_DEFINED */

%}

typedef
vector_3_float_t0ype =
$extype_struct "vec3f_t" of {
  V= @[float][3]
}

stadef vec3f = vector_3_float_t0ype // local shorthand

fun add_vec3f_vec3f (&vec3f, &vec3f): vec3f
fun mul_float_vec3f (float, &vec3f): vec3f
fun neg_vec3f (&vec3f): vec3f
fun sub_vec3f_vec3f (&vec3f, &vec3f): vec3f
fun length_sq_vec3f (&vec3f): float
fun length_vec3f (&vec3f): float
fun dotprod_vec3f_vec3f (&vec3f, &vec3f): float
fun{}
equal_vec3f$eps (): float
fun
equal_vec3f_vec3f (&vec3f, &vec3f): bool
fun
fprint_vec3f (FILEref, &vec3f): void
fun
print_vec3f (&vec3f): void

//
overload + with add_vec3f_vec3f of 10
overload * with mul_float_vec3f of 10
overload ~ with neg_vec3f of 10
overload - with sub_vec3f_vec3f of 10
overload .length_sq with length_sq_vec3f of 10
overload .length with length_vec3f of 10
overload dotprod with dotprod_vec3f_vec3f of 10
overload = with equal_vec3f_vec3f of 10
overload fprint with fprint_vec3f of 10
overload print with print_vec3f of 10
//

fun
crossprod_vec3f_vec3f (&vec3f, &vec3f): vec3f

fun
vec3f_init (&vec3f? >> _, float, float, float): void
overload .init with vec3f_init of 10

fun
vec3f_get_x (&vec3f): float
fun
vec3f_get_y (&vec3f): float
fun
vec3f_get_z (&vec3f): float

overload .x with vec3f_get_x of 10
overload .y with vec3f_get_y of 10
overload .z with vec3f_get_z of 10

fun
vec3f_set_x (&vec3f, float): void
fun
vec3f_set_y (&vec3f, float): void
fun
vec3f_set_z (&vec3f, float): void

overload .x with vec3f_set_x of 10
overload .y with vec3f_set_y of 10
overload .z with vec3f_set_z of 10

(* ****** ****** *)

%{^

#ifndef ATS_VEC4F_DEFINED
#define ATS_VEC4F_DEFINED

typedef
struct {
  float V[4];
} vec4f_t;

#endif /* ATS_VEC4F_DEFINED */

%}

typedef
vector_4_float_t0ype =
$extype_struct "vec4f_t" of {
  V= @[float][4]
}

stadef vec4f = vector_4_float_t0ype // local shorthand

fun add_vec4f_vec4f (&vec4f, &vec4f): vec4f
fun mul_float_vec4f (float, &vec4f): vec4f
fun neg_vec4f (&vec4f): vec4f
fun sub_vec4f_vec4f (&vec4f, &vec4f): vec4f
fun length_sq_vec4f (&vec4f): float
fun length_vec4f (&vec4f): float
fun dotprod_vec4f_vec4f (&vec4f, &vec4f): float
fun{}
equal_vec4f$eps (): float
fun
equal_vec4f_vec4f (&vec4f, &vec4f): bool
fun
fprint_vec4f (FILEref, &vec4f): void
fun
print_vec4f (&vec4f): void

//
overload + with add_vec4f_vec4f
overload * with mul_float_vec4f
overload ~ with neg_vec4f
overload - with sub_vec4f_vec4f
overload .length_sq with length_sq_vec4f
overload .length with length_vec4f
overload dotprod with dotprod_vec4f_vec4f
overload = with equal_vec4f_vec4f
overload fprint with fprint_vec4f
overload print with print_vec4f
//

fun
vec4f_init (&vec4f? >> _, float, float, float, float): void
overload .init with vec4f_init

fun
vec4f_get_x (&vec4f): float
fun
vec4f_get_y (&vec4f): float
fun
vec4f_get_z (&vec4f): float
fun
vec4f_get_w (&vec4f): float

overload .x with vec4f_get_x
overload .y with vec4f_get_y
overload .z with vec4f_get_z
overload .w with vec4f_get_w

fun
vec4f_set_x (&vec4f, float): void
fun
vec4f_set_y (&vec4f, float): void
fun
vec4f_set_z (&vec4f, float): void
fun
vec4f_set_w (&vec4f, float): void

overload .x with vec4f_set_x
overload .y with vec4f_set_y
overload .z with vec4f_set_z
overload .w with vec4f_set_w


(* ****** ****** *)
