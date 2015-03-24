#define ATS_PACKNAME "PLAYGROUND.vector3"

%{^

typedef
struct {
  float V[3];
} vec3f_t;

%}

typedef T = float
#define NDIM 3

typedef
vector_t0ype =
$extype_struct "vec3f_t" of {
  V= @[T][NDIM]
}

stadef vec = vector_t0ype // local shorthand

#include "./SHARE/vector.hats"

fun
vector_init (&vec? >> vec, T, T, T): void
