//
#define ATS_PACKNAME "PLAYGROUND.mat3x3f"
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

staload _ = "../DATS/vec3f.dats"

(* ****** ****** *)

extern
fun{a:t@ype}
gdet_treshold (): a

implement
gdet_treshold<float> () = 1e-7f
implement
gdet_treshold<double> () = 1e-15

(* ****** ****** *)
//
typedef T = float
#define NROW 3
#define NCOL 3
typedef COL_T = vec3f
typedef mat = mat3x3f
//
(* ****** ****** *)
//
extern
fun{vt:vt@ype}
mat_init$fwork (natLt(NROW), natLt(NCOL), &(vt)): T
//
extern
fun{vt:vt@ype}
mat_init_env (
  mat: &mat? >> _, env: &(vt)
): void // end of [mat_init_env]
//
(* ****** ****** *)
//
implement{vt}
mat_init_env (m, env) = {
//
fun aux_col {lres:addr} (
  pf_res: !COL_T? @ lres >> COL_T @ lres
| pres: ptr lres, i: natLt(NCOL), env: &(vt)
): void = loop (pres->V, i, env) where {
//
fun loop (res: &(@[T?][NROW]) >> @[T][NROW], i: natLt(NCOL), env: &(vt)): void = {
//
var j: int = 0
prval [lres:addr] EQADDR () = eqaddr_make_ptr (addr@(res))
var p = addr@(res)
prvar pf0 = array_v_nil {T} ()
prvar pf1 = view@(res)
//
val () =
while* {j:nat | j <= NROW} .<NROW-j>. (
  j: int (j)
, p: ptr (lres + j*sizeof(T))
, pf0: array_v (T, lres, j)
, pf1: array_v (T?, lres+j*sizeof(T), NROW-j)
) : (
  pf0: array_v (T, lres, NROW)
, pf1: array_v (T?, lres+j*sizeof(T), 0)
) => (
  j < NROW
) {
//
  prval (pf_at, pf1_res) = array_v_uncons {T?} (pf1)
  prval () = pf1 := pf1_res
  //
  val () = ptr_set<T> (pf_at | p, mat_init$fwork<vt> (j, i, env))
  val () = p := ptr1_succ<T> (p)
  //
  prval () = pf0 := array_v_extend {T} (pf0, pf_at)
  val () = j := j + 1
//
} // end of [val]
//
prval () = view@(res) := pf0
prval () = array_v_unnil {T?} (pf1)
//
} (* end of [loop] *)
//
} (* end of [aux_col] *)
//
fun
aux (res: &(@[COL_T?][NCOL]) >> @[COL_T][NCOL], env: &vt): void = {
//
var i: int = 0
prval [lres:addr] EQADDR () = eqaddr_make_ptr (addr@(res))
var p = addr@(res)
prvar pf0 = array_v_nil {COL_T} ()
prvar pf1 = view@(res)
//
val () =
while* {i:nat | i <= NCOL} .<NCOL-i>. (
  i: int (i)
, p: ptr (lres + i*sizeof(COL_T))
, pf0: array_v (COL_T, lres, i)
, pf1: array_v (COL_T?, lres+i*sizeof(COL_T), NCOL-i)
) : (
  pf0: array_v (COL_T, lres, NCOL)
, pf1: array_v (COL_T?, lres+i*sizeof(COL_T), 0)
) => (
  i < NCOL
) {
//
  prval (pf_at, pf1_res) = array_v_uncons {COL_T?} (pf1)
  prval () = pf1 := pf1_res
  //
  val () = aux_col (pf_at | p, i, env)
  val () = p := ptr1_succ<COL_T> (p)
  //
  prval () = pf0 := array_v_extend {COL_T} (pf0, pf_at)
  val () = i := i + 1
//
} // end of [val]
//
prval () = view@(res) := pf0
prval () = array_v_unnil {COL_T?} (pf1)
//
} (* end of [aux] *)
//
val () = aux (m.M, env)
//
} (* end of [mat_init_env] *)

(* ****** ****** *)

//
implement
mat3x3f_init1 (m, x) = {
//
implement
mat_init$fwork<void> (c, r, env) = x
//
var env = ()
val () = mat_init_env<void> (m, env)
//
} (* end of [mat3x3f_init1] *)
//
implement
mat3x3f_init9 (m, s00, s10, s20, s01, s11, s21, s02, s12, s22) = {
//
var c0: COL_T
var c1: COL_T
var c2: COL_T
//
val () = c0.init (s00, s10, s20)
val () = c1.init (s01, s11, s21)
val () = c2.init (s02, s12, s22)
//
val () = mat3x3f_init3_vec3f (m, c0, c1, c2)
//
} (* end of [mat3x3f_init9] *)
//
implement
mat3x3f_init3_vec3f (m, col0, col1, col2) = {
//
fun
aux (m: &(@[INV(COL_T)][NCOL])? >> _, c0: &COL_T, c1: &COL_T, c2: &COL_T): void = {
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
#define :: array_v_cons
//
prval pf3_nil = array_v_unnil_nil (pf3_arr)
prval () = view@(m) := pf1_at :: pf2_at :: pf3_at :: pf3_nil
//
} (* end of [aux] *)
//
val () = aux (m.M, col0, col1, col2)
//
} (* end of [mat3x3f_init3_vec3f] *)

implement
mat3x3f_init_arrptr {n} (m, arr) = {
prval [larr:addr] EQADDR () = eqaddr_make_ptr (addr@(arr))
//
absvt@ype VT = void
viewdef V = (@[T][n] @ larr)
prval (dec, enc) = make_iso_v_vt {V} {VT} ()
//
implement
mat_init$fwork<VT> (i, j, env) = res where {
  prval pf = dec (env)
  val ix = i*NCOL + j
  val res = arr.[ix]
  prval () = enc (env, pf)
}
//
var env = ()
prval () = enc (env, view@arr)
//
val () = mat_init_env<VT> (m, env)
//
prval () = view@arr := dec (env)
//
} (* end of [mat3x3f_init_arrptr] *)

implement
mat3x3f_get_int_int (m, r, c) = m.M.[c].V.[r]
(*
implement
mat3x3f_get_int (m, i) = let val r = i % NROW; val c = i / NROW in m.M[c].V[r] end
*)
implement
mat3x3f_set_int_int (m, r, c, x) = m.M.[c].V.[r] := x
(*
implement
mat3x3f_set_int (m, i, x) = ?
*)

implement
add_mat3x3f_mat3x3f (x, y) = let
//
prval [lx:addr] EQADDR () = eqaddr_make_ptr (addr@(x))
prval [ly:addr] EQADDR () = eqaddr_make_ptr (addr@(y))
//
absvt@ype VT = void
viewdef V = (mat @ lx, mat @ ly)
prval (dec, enc) = make_iso_v_vt {V} {VT} ()
//
implement
mat_init$fwork<VT> (i, j, env) = res where {
  prval pf = dec (env)
  val res = gadd_val_val<T> (x.M.[i].V.[j], y.M.[i].V.[j])
  prval () = enc (env, pf)
}
//
var env = ()
prval () = enc (env, (view@x, view@y))
//
var res: mat
val () = mat_init_env<VT> (res, env)
//
prval (pf0, pf1) = dec (env)
prval () = view@x := pf0
and () = view@y := pf1
//
in
  res
end

implement
add_float_mat3x3f (s, x) = let
//
prval [lx:addr] EQADDR () = eqaddr_make_ptr (addr@(x))
//
absvt@ype VT = void
viewdef V = (mat @ lx)
prval (dec, enc) = make_iso_v_vt {V} {VT} ()
//
implement
mat_init$fwork<VT> (i, j, env) = res where {
  prval pf = dec (env)
  val res = gadd_val_val<T> (s, x.M.[i].V.[j])
  prval () = enc (env, pf)
}
//
var env = ()
prval () = enc (env, (view@x))
//
var res: mat
val () = mat_init_env<VT> (res, env)
//
prval pf0 = dec (env)
prval () = view@x := pf0
//
in
  res
end

implement
mul_float_mat3x3f (s, x) = let
//
prval [lx:addr] EQADDR () = eqaddr_make_ptr (addr@(x))
//
absvt@ype VT = void
viewdef V = (mat @ lx)
prval (dec, enc) = make_iso_v_vt {V} {VT} ()
//
implement
mat_init$fwork<VT> (i, j, env) = res where {
  prval pf = dec (env)
  val res = gmul_val_val<T> (s, x.M.[i].V.[j])
  prval () = enc (env, pf)
}
//
var env = ()
prval () = enc (env, (view@x))
//
var res: mat
val () = mat_init_env<VT> (res, env)
//
prval pf0 = dec (env)
prval () = view@x := pf0
//
in
  res
end

implement
mul_mat3x3f_mat3x3f (x, y) = let
//
prval [lx:addr] EQADDR () = eqaddr_make_ptr (addr@(x))
prval [ly:addr] EQADDR () = eqaddr_make_ptr (addr@(y))
//
absvt@ype VT = void
viewdef V = (mat @ lx, mat @ ly)
prval (dec, enc) = make_iso_v_vt {V} {VT} ()
//
implement
mat_init$fwork<VT> (i, j, env) = res where {
  var row: COL_T
  //
  implement
  vec3f_init$fwork<VT>(k, env) = res where {
    prval pf = dec (env)
    val res = x.M.[k].V.[i]
    prval () = enc (env, pf)
  }
  //
  val () = vec3f_init_env<VT> (row, env)
  //
  prval pf = dec (env)
  val res = dotprod_vec3f_vec3f (y.M.[j], row)
  prval () = enc (env, pf)
}
//
var env = ()
prval () = enc (env, (view@x, view@y))
//
var res: mat
val () = mat_init_env<VT> (res, env)
//
prval (pf0, pf1) = dec (env)
prval () = view@x := pf0
and () = view@y := pf1
//
in
  res
end

implement
sub_mat3x3f_mat3x3f (x, y) = let
//
prval [lx:addr] EQADDR () = eqaddr_make_ptr (addr@(x))
prval [ly:addr] EQADDR () = eqaddr_make_ptr (addr@(y))
//
absvt@ype VT = void
viewdef V = (mat @ lx, mat @ ly)
prval (dec, enc) = make_iso_v_vt {V} {VT} ()
//
implement
mat_init$fwork<VT> (i, j, env) = res where {
  prval pf = dec (env)
  val res = gsub_val_val<T> (x.M.[i].V.[j], y.M.[i].V.[j])
  prval () = enc (env, pf)
}
//
var env = ()
prval () = enc (env, (view@x, view@y))
//
var res: mat
val () = mat_init_env<VT> (res, env)
//
prval (pf0, pf1) = dec (env)
prval () = view@x := pf0
and () = view@y := pf1
//
in
  res
end

implement
neg_mat3x3f (x) = let
//
prval [lx:addr] EQADDR () = eqaddr_make_ptr (addr@(x))
//
absvt@ype VT = void
viewdef V = (mat @ lx)
prval (dec, enc) = make_iso_v_vt {V} {VT} ()
//
implement
mat_init$fwork<VT> (i, j, env) = res where {
  prval pf = dec (env)
  val res = gneg_val<T> (x.M.[i].V.[j])
  prval () = enc (env, pf)
}
//
var env = ()
prval () = enc (env, (view@x))
//
var res: mat
val () = mat_init_env<VT> (res, env)
//
prval pf0 = dec (env)
prval () = view@x := pf0
//
in
  res
end

extern
fun{N:type}
invert_mat3x3f_mat3x3f_opt {n:nat | n < 2} (
  pf: tieq (N, n)
| m: &mat3x3f, res: &mat3x3f? >> opt (mat3x3f, b)
) : #[b:bool | n == 0 && b == true || n == 1] bool b

implement{N}
invert_mat3x3f_mat3x3f_opt {n} (pf | m, res) = let
//
  macdef mul (x, y) = gmul_val_val<T>(,(x), ,(y))
  macdef neg (x) = gneg_val<T>(,(x))
  macdef add (x, y) = gadd_val_val<T>(,(x), ,(y))
  macdef sub (x, y) = gsub_val_val<T>(,(x), ,(y))
//
val det = add (sub (mul (m[0, 0], sub (mul (m[1, 1], m[2, 2]), mul (m[2, 1], m[1, 2]))),
                    mul (m[0, 1], sub (mul (m[1, 0], m[2, 2]), mul (m[1, 2], m[2, 0])))),
               mul (m[0, 2], sub (mul (m[1, 0], m[2, 1]), mul (m[1, 1], m[2, 0]))))
val () = (println!("m = "); print_mat3x3f (m); print_newline ())
val () = println!("sub00 = ", mul (m[0, 0], sub (mul (m[1, 1], m[2, 2]), mul (m[2, 1], m[1, 2]))))
val () = println!("sub01 = ", mul (m[0, 1], sub (mul (m[1, 0], m[2, 2]), mul (m[1, 2], m[2, 0]))))
val () = println!("sub02 = ", mul (m[0, 2], sub (mul (m[1, 0], m[2, 1]), mul (m[1, 1], m[2, 0]))))
val () = println!("m[1,1] = ", m[1,1])
val () = println!("m[2,2] = ", m[2,2])
val () = println!("determinant is: ", det)
//
val ck = tieq2int<N> (pf | (*void*))
//
macdef calc = let
  val invdet = gdiv_val_val<T> (gnumber_int<T>(1), det);
in
  mat3x3f_init9 (
    res,
    mul (sub (mul (m[1, 1], m[2, 2]), mul (m[2, 1], m[1, 2])), invdet),
    mul (sub (mul (m[1, 2], m[2, 0]), mul (m[1, 0], m[2, 2])), invdet),
    mul (sub (mul (m[1, 0], m[2, 1]), mul (m[2, 0], m[1, 1])), invdet),
    mul (sub (mul (m[0, 2], m[2, 1]), mul (m[0, 1], m[2, 2])), invdet),
    mul (sub (mul (m[0, 0], m[2, 2]), mul (m[0, 2], m[2, 0])), invdet),
    mul (sub (mul (m[2, 0], m[0, 1]), mul (m[0, 0], m[2, 1])), invdet),
    mul (sub (mul (m[0, 1], m[1, 2]), mul (m[0, 2], m[1, 1])), invdet),
    mul (sub (mul (m[1, 0], m[0, 2]), mul (m[0, 0], m[1, 2])), invdet),
    mul (sub (mul (m[0, 0], m[1, 1]), mul (m[1, 0], m[0, 1])), invdet)
  )
end // end of [macdef]
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
  end
//
)
//
end

implement
invert_mat3x3f (m) = let
  var res: mat
  val+ true = invert_mat3x3f_mat3x3f_opt<fS(0)> (TIEQZ() | m, res)
  prval () = opt_unsome {mat} (res)
in
  res
end

implement
invert_mat3x3f_mat3x3f (m, res) =
  invert_mat3x3f_mat3x3f_opt<fS(1)> (TIEQS(TIEQZ()) | m, res)
// end of [invert_mat3x3f_mat3x3f]

implement
transpose_mat3x3f (m) = let
//
var res: mat
//
implement
mat_init$fwork<mat> (i, j, env) = env.M.[i].V.[j]
//
val () = mat_init_env<mat> (res, m)
//
in
  res
end

implement
identity_mat3x3f () = let
//
implement
mat_init$fwork<void> (c, r, env) =
  gnumber_int<T> (bool2int(c = r))
//
var res: mat
var env = ()
val () = mat_init_env<void> (res, env)  
//
in
  res
end

implement
mul_vec3f_mat3x3f (v, m) = let
//
prval [lv:addr] EQADDR () = eqaddr_make_ptr (addr@(v))
prval [lm:addr] EQADDR () = eqaddr_make_ptr (addr@(m))
//
absvt@ype VT = void
viewdef V = (COL_T @ lv, mat @ lm)
prval (dec, enc) = make_iso_v_vt {V} {VT} ()
//
implement
vec3f_init$fwork<VT> (i, env) = res where {
  prval pf = dec (env)
  val res = dotprod_vec3f_vec3f (v, m.M.[i])
  prval () = enc (env, pf)
}
//
var env = ()
prval () = enc (env, (view@v, view@m))
//
var res: COL_T
val () = vec3f_init_env<VT> (res, env)
//
prval (pf0, pf1) = dec (env)
prval () = view@v := pf0
and () = view@m := pf1
//
in
  res
end

implement
fprint_mat3x3f (out, m) = {
//
val () = fprint (out, "(")
//
implement
fprint_ref<COL_T> (out, c) =
  fprint_vec3f (out, c)
//
val () = fprint_array_int<COL_T> (out, m.M, NCOL)
//
val () = fprint (out, ")")
//
} (* end of [fprint_mat3x3f] *)

implement
print_mat3x3f (m) = fprint_mat3x3f (stdout_ref, m)
