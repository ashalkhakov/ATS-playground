#include
"share/atspre_staload.hats"

staload "libc/SATS/math.sats" // NOTE: requires -lm during compilation
staload _ = "libc/DATS/math.dats"

staload "../SATS/vector.sats"
staload _ = "../DATS/vec3f.dats"

staload "../SATS/matrix.sats"
staload _ = "../DATS/mat3x3f.dats"

(* ****** ****** *)

// Precision for floats and doubles
#define FLOAT_PRECISION 1e-6f
#define DOUBLE_PRECISION 1e-15

macdef
EXPECT_NEAR (x, e, eps) = assertloc (abs (,(x) - ,(e)) < ,(eps))

fun
test_compare () = let
  var v0: vec3f
  var v1: vec3f
  var v2: vec3f
  var v3: vec3f
  val () = vec3f_init3 (v0, 1.0f, 0.0f, 0.0f)
  val () = vec3f_init3 (v1, 1.0f, 1.0f, 1.0f)
  val () = vec3f_init3 (v2, 0.5f, 1.0f, 0.0f)
  val () = vec3f_init3 (v3, 0.0f, 1.0f, 2.0f)
  
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

fun
test_mat3x3f (): void = let
#define precision FLOAT_PRECISION
//
val () = println!("test_mat3x3f BEG")
//
val () = {
  var m: mat3x3f
  //
  val () = mat3x3f_init1 (m, 3.1f)
  val () = (print_mat3x3f (m); print_newline ())
  //
} // end of [val]
//
val () = {
  var m: mat3x3f
  val () = mat3x3f_init9(m,
    3.7f, 2.4f, 6.4f,
    1.1f, 5.2f, 6.4f,
    2.7f, 7.4f, 0.1f);
  val () = EXPECT_NEAR (3.7f, m[0, 0], precision);
  val () = EXPECT_NEAR (2.4f, m[1, 0], precision);
  val () = EXPECT_NEAR (6.4f, m[2, 0], precision);
  val () = EXPECT_NEAR (1.1f, m[0, 1], precision);
  val () = EXPECT_NEAR (5.2f, m[1, 1], precision);
  val () = EXPECT_NEAR (6.4f, m[2, 1], precision);
  val () = EXPECT_NEAR (2.7f, m[0, 2], precision);
  val () = EXPECT_NEAR (7.4f, m[1, 2], precision);
  val () = EXPECT_NEAR (0.1f, m[2, 2], precision);

  val () = println!("transpose bef:")  
  val () = (print_mat3x3f (m); print_newline ())
  var m2 = transpose_mat3x3f (m)
  val () = println!("transpose aft:")
  val () = (print_mat3x3f (m2); print_newline ())

  var m3 = identity_mat3x3f ()
  var m4 = mul_mat3x3f_mat3x3f (m3, m)
  val () = println!("multiplication result (by identity):")
  val () = (print_mat3x3f (m4); print_newline ())

  var m5: mat3x3f
  val () = mat3x3f_init1 (m5, 0.2f)
  var m6 = mul_float_mat3x3f (2.0f, m5)
  val () = println!("multiplication result (by scalar):")
  val () = (print_mat3x3f (m6); print_newline ())

  // test matrix multiplication
  var mrotx: mat3x3f
  val () =
    mat3x3f_init9
      (mrotx, 1.0f, 0.0f, 0.0f,
              0.0f, vx, vy,
              0.0f, ~vy, vx) where {
    val angle = (g0float2float_double_float(M_PI)) / 4.0f
    val vx = cos (angle)
    val vy = sin (angle)
  } // end of [val]
  var v0: vec3f
  val () = vec3f_init3 (v0, 1.0f, 1.0f, 0.0f)
  var v1 = mul_vec3f_mat3x3f (v0, mrotx)
  val () = println!("vec bef rotation:")
  val () = (print_vec3f (v0); print_newline ())
  val () = println!("vec aft rotation:")
  val () = (print_vec3f (v1); print_newline ())
  
  // test matrix inverse
  var m_inv = invert_mat3x3f (mrotx)
  val () = (println! ("m_inv: "); print_mat3x3f (m_inv); print_newline ())
  var mident = mul_mat3x3f_mat3x3f (m_inv, mrotx)
  val () = (println! ("near-identity matrix: "); print_mat3x3f (mident); print_newline ())
} // end of [val]
//
val () = {
  var m = identity_mat3x3f ()
  val () = (print_mat3x3f (m); print_newline ())
} // end of [val]
//
val () = {
  var m1 = identity_mat3x3f ()
  var m2 = identity_mat3x3f ()
  var m3 = mul_mat3x3f_mat3x3f (m1, m2)
  val () = (print_mat3x3f (m3); print_newline ())
} // end of [val]
//
val () = println!("test_mat3x3f END")
//
in
end

implement
main0 () = let
var v1: vec3f
var v2: vec3f
var v3: vec3f
val () = v1.init (1.0f, 0.0f, 0.0f)
val () = v2.init (0.0f, 1.0f, 0.0f)
// approach A: just use the predefined operators
// pros: simple
// cons: lots of temporary variables (for lvalues)
var v3_tmp = 2.0f * v2
val () = v3 := v1 + v3_tmp
//
val () = println!("v3 = ", v3)
// approach B: use a loop
// pros: no temporary variables, first-order, vectorizable
// cons: syntactic overhead due to type annotation/proof construction
absvt@ype VT = void
viewdef V = (vec3f @ v1, vec3f @ v2)
prval (dec, enc) = make_iso_v_vt {V} {VT} ()
//
implement
vec3f_init$fwork<VT> (i, env) = res where {
  prval pf = dec (env)
  val res = 2.0f * v1[i] + 0.5f * v2[i] + 1.0f
  prval () = enc (env, pf)
}
//
var env = ()
prval () = enc (env, (view@v1, view@v2))
//
val () = vec3f_init_env<VT> (v3, env)
//
prval (pf0, pf1) = dec (env)
prval () = view@v1 := pf0
and () = view@v2 := pf1
//
val () = println!("v3 = ", v3)
//
val () = test_compare ()
//
val () = test_mat3x3f ()
in
end
