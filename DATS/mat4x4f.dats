//
#define ATS_PACKNAME "PLAYGROUND.mat4x4f"
#define ATS_DYNLOADFLAG 0
//
#include
"share/atspre_staload.hats"
//
staload "../SATS/vector.sats"
staload "../SATS/matrix.sats"

staload _ = "prelude/DATS/gnumber.dats"
staload _ = "prelude/DATS/SHARE/gnumber_float.dats"
staload _ = "prelude/DATS/gorder.dats"

staload "libc/SATS/math.sats" // NOTE: requires -lm during compilation
staload _ = "libc/DATS/math.dats"

staload "libats/SATS/typeval.sats"
staload _ = "libats/DATS/typeval.dats"

staload _ = "./matrix.dats"

// we will need some implementation details
staload "./vec4f.dats"

(* ****** ****** *)
//
typedef T = float
#define NROW 4
#define NCOL 4
typedef vec = vec4f
typedef COL_T = vec4f
typedef mat = mat4x4f
//
(* ****** ****** *)

#include "./SHARE/matrix.hats"

(* ****** ****** *)

implement
mat4x4f_init1 (m, x) = mat_init1 (m, x)
//
implement
mat4x4f_init16 (
  m,
  s00, s10, s20, s30,
  s01, s11, s21, s31,
  s02, s12, s22, s32,
  s03, s13, s23, s33
) = {
//
var c0: COL_T
var c1: COL_T
var c2: COL_T
var c3: COL_T
//
val () = c0.init (s00, s10, s20, s30)
val () = c1.init (s01, s11, s21, s31)
val () = c2.init (s02, s12, s22, s32)
val () = c3.init (s03, s13, s23, s33)
//
val () = mat4x4f_init4_vec4f (m, c0, c1, c2, c3)
//
} (* end of [mat4x4f_init16] *)
//
implement
mat4x4f_init4_vec4f (m, col0, col1, col2, col3) = {
//
fun
aux (m: &(@[INV(COL_T)][NCOL])? >> _, c0: &COL_T, c1: &COL_T, c2: &COL_T, c3: &COL_T): void = {
//
prval pf_arr = view@(m)
var pm = addr@(m)
//
prval (pf1_at, pf1_arr) = array_v_uncons {COL_T?} (pf_arr)
val () = ptr_set<COL_T> (pf1_at | pm, c0)
//
val () = pm := ptr1_succ<COL_T> (pm)
prval (pf2_at, pf2_arr) = array_v_uncons {COL_T?} (pf1_arr)
val () = ptr_set<COL_T> (pf2_at | pm, c1)
//
val () = pm := ptr1_succ<COL_T> (pm)
prval (pf3_at, pf3_arr) = array_v_uncons {COL_T?} (pf2_arr)
val () = ptr_set<COL_T> (pf3_at | pm, c2)
//
val () = pm := ptr1_succ<COL_T> (pm)
prval (pf4_at, pf4_arr) = array_v_uncons {COL_T?} (pf3_arr)
val () = ptr_set<COL_T> (pf4_at | pm, c3)
//
#define :: array_v_cons
//
prval pf4_nil = array_v_unnil_nil (pf4_arr)
prval () = view@(m) := pf1_at :: pf2_at :: pf3_at :: pf4_at :: pf4_nil
//
} (* end of [aux] *)
//
val () = aux (m.M, col0, col1, col2, col3)
//
} (* end of [mat4x4f_init4_vec4] *)
//
implement
mat4x4f_init_arrptr {n} (res, arr) = mat_init_arrptr (res, arr)
//
implement
mat4x4f_get_int_int (m, row, col) = m.M.[col].V.[row]
(*
fun
mat4x4f_get_int (&mat4x4f, i: natLt(4*4)): float
*)
implement
mat4x4f_set_int_int (m, row, col, x) = m.M.[col].V.[row] := x
(*
fun
mat4x4f_set_int (&mat4x4f, i: natLt(3*3), float): void
*)

implement
add_mat4x4f_mat4x4f (x, y) = add_mat_mat (x, y)
//
implement
add_float_mat4x4f (s, x) = add_T_mat (s, x)
//
implement
mul_float_mat4x4f (s, x) = mul_T_mat (s, x)
//
implement
mul_mat4x4f_mat4x4f (x, y) = mul_mat_mat (x, y)
//
implement
sub_mat4x4f_mat4x4f (x, y) = sub_mat_mat (x, y)
//
implement
neg_mat4x4f (x) = neg_mat (x)
//
extern
fun{N:type}
invert_mat4x4f_mat4x4f_opt {n:nat | n < 2} (
  pf: tieq (N, n)
| m: &mat4x4f, res: &mat4x4f? >> opt (mat4x4f, b)
) : #[b:bool | n == 0 && b == true || n == 1] bool b
//
implement{N}
invert_mat4x4f_mat4x4f_opt {n} (pf | m, res) = let
//
macdef mul (x, y) = gmul_val_val<T>(,(x), ,(y))
macdef neg (x) = gneg_val<T>(,(x))
macdef pos (x) = (,(x))
macdef add (x, y) = gadd_val_val<T>(,(x), ,(y))
macdef sub (x, y) = gsub_val_val<T>(,(x), ,(y))
//
// kudos go to Anders Gustafsson on this one!
//
macdef det2x2 (a, b, c, d) = sub (mul (,(a), ,(b)), mul (,(c), ,(d)))
macdef wrk0 (a, b, c) = add (,(a), sub (,(b), ,(c)))
macdef wrk1 (a, b, c) = sub (,(a), add (,(b), ,(c)))
//
val s0 = det2x2 (m[0,0], m[1,1], m[1,0], m[0,1])
val s1 = det2x2 (m[0,0], m[1,2], m[1,0], m[0,2])
val s2 = det2x2 (m[0,0], m[1,3], m[1,0], m[0,3])
val s3 = det2x2 (m[0,1], m[1,2], m[1,1], m[0,2])
val s4 = det2x2 (m[0,1], m[1,3], m[1,1], m[0,3])
val s5 = det2x2 (m[0,2], m[1,3], m[1,2], m[0,3])
//
val c5 = det2x2 (m[2, 2], m[3, 3], m[3, 2], m[2, 3])
val c4 = det2x2 (m[2, 1], m[3, 3], m[3, 1], m[2, 3])
val c3 = det2x2 (m[2, 1], m[3, 2], m[3, 1], m[2, 2])
val c2 = det2x2 (m[2, 0], m[3, 3], m[3, 0], m[2, 3])
val c1 = det2x2 (m[2, 0], m[3, 2], m[3, 0], m[2, 2])
val c0 = det2x2 (m[2, 0], m[3, 1], m[3, 0], m[2, 1])
//
val det = add (det2x2 (s0, c5, s1, c4), add (mul (s2, c3), add (det2x2 (s3, c2, s4, c1), mul (s5, c0))))
//
val ck = tieq2int<N> (pf | (*void*))
//
macdef calc = {
//
val invdet = gdiv_val_val<T> (gnumber_int<T> (1), det)
//
val () =
  mat4x4f_init16 (
    res,
    //
    mul (wrk1 (mul (pos (m[1,1]), c5), mul (m[1,2], c4), mul (m[1,3], c3)), invdet),
    mul (wrk0 (mul (neg (m[1,0]), c5), mul (m[1,2], c2), mul (m[1,3], c1)), invdet),
    mul (wrk1 (mul (pos (m[1,0]), c4), mul (m[1,1], c2), mul (m[1,3], c0)), invdet),
    mul (wrk0 (mul (neg (m[1,0]), c3), mul (m[1,1], c1), mul (m[1,2], c0)), invdet),
    //
    mul (wrk0 (mul (neg (m[0,1]), c5), mul (m[0,2], c4), mul (m[0,3], c3)), invdet),
    mul (wrk1 (mul (pos (m[0,0]), c5), mul (m[0,2], c2), mul (m[0,3], c1)), invdet),
    mul (wrk0 (mul (neg (m[0,0]), c4), mul (m[0,1], c2), mul (m[0,3], c0)), invdet),
    mul (wrk1 (mul (pos (m[0,0]), c3), mul (m[0,1], c1), mul (m[0,2], c0)), invdet),
    //
    mul (wrk1 (mul (pos (m[3,1]), s5), mul (m[3,2], s4), mul (m[3,3], s3)), invdet),
    mul (wrk0 (mul (neg (m[3,0]), s5), mul (m[3,2], s2), mul (m[3,3], s1)), invdet),
    mul (wrk1 (mul (pos (m[3,0]), s4), mul (m[3,1], s2), mul (m[3,3], s0)), invdet),
    mul (wrk0 (mul (neg (m[3,0]), s3), mul (m[3,1], s1), mul (m[3,2], s0)), invdet),
    //
    mul (wrk0 (mul (neg (m[2,1]), s5), mul (m[2,2], s4), mul (m[2,3], s3)), invdet),
    mul (wrk1 (mul (neg (m[2,0]), s5), mul (m[2,2], s2), mul (m[2,3], s1)), invdet),
    mul (wrk0 (mul (neg (m[2,0]), s4), mul (m[2,1], s2), mul (m[2,3], s0)), invdet),
    mul (wrk1 (mul (pos (m[2,0]), s3), mul (m[2,1], s1), mul (m[2,2], s0)), invdet)
    //
  ) // end of[val]
} // end of [macdef]
//
in
//
if ck = 0 then let
  val () = calc
  prval () = opt_some {mat} (res)
in
  true
end else (
//
  if glt_val_val<T> (gabs_val<T> (det), gdet_treshold<T> ()) then let
    prval () = opt_none {mat} (res)
  in
    false
  end else let
    val () = calc
    prval () = opt_some {mat} (res)
  in
    true
  end // end of [if]
//
)
//
end // end of [invert_mat4x4f_mat4x4f_opt]
//
implement
invert_mat4x4f (m) = let
  var res: mat
  val+ true = invert_mat4x4f_mat4x4f_opt<fS(0)> (TIEQZ() | m, res)
  prval () = opt_unsome {mat} (res)
in
  res
end // end of [invert_mat4x4f]
//
implement
invert_mat4x4f_mat4x4f (m, res) =
  invert_mat4x4f_mat4x4f_opt<fS(1)> (TIEQS(TIEQZ()) | m, res)
// end of [invert_mat4x4f_mat4x4f]
//
implement
transpose_mat4x4f (x) = transpose_mat (x)
implement
identity_mat4x4f (x) = identity_mat (x)
implement
mul_vec4f_mat4x4f (v, x) = mul_vec_mat (v, x)
implement
fprint_mat4x4f (out, x) = fprint_mat (out, x)
implement
print_mat4x4f (x) = print_mat (x)

