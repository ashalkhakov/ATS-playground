//
// Author: Artyom Shakhakov (artyom DOT shalkhakov AT gmail DOT com)
// Time: May, 2011
// Time: Dec, 2015 (ported to ATS2)
//

#include
"share/atspre_staload.hats"

staload STDIO = "libc/SATS/stdio.sats"


datatype PIXELTYPE (t@ype) =
  | PTrgb (uint32)
  | PTrgba (uint32)
  | PTbw (uint8)

macdef
implies (x, y) = (if ,(x) then ,(y) else false)

(* ****** ****** *)

extern
praxi
opt_reset
  {a:t0p}{b:bool}(x: !opt(INV(a), b) >> opt (a, false)):<prf> void

local

macrodef
rec
auxlist
  (f, xs, y) =
(
//
if iscons! (xs) then
  `(let prval () = ,(f) (,(car! xs)) in ,(auxlist (f, cdr! xs, y)) end)
else y // end of [if]
//
) // end of [auxlist]

in (* in of [local] *)

macdef
opt_none_mac (x) =
,(
  if islist! (x) then auxlist(`(opt_none), x, `()) else `(opt_none ,(x))
)

macdef
opt_some_mac (x) =
,(
  if islist! (x) then auxlist (`(opt_some), x, `()) else `(opt_some ,(x))
)

macdef
opt_unsome_mac (x) =
,(
  if islist! (x) then auxlist (`(opt_unsome), x, `()) else `(opt_unsome ,(x))
)

macdef
opt_clear_mac (x) =
,(
  if islist! (x) then auxlist (`(opt_clear), x, `()) else `(opt_clear ,(x))
)

macdef
opt_reset_mac (x) =
,(
  if islist! (x) then auxlist (`(opt_reset), x, `()) else `(opt_reset ,(x))
) // end of [opt_reset_mac]

macdef
opt_clear_mac(x) =
,(
  if islist! (x) then auxlist (`(opt_clear), x, `()) else `(opt_clear ,(x))
) // end of [opt_clear_mac]

end // end of [local]

(* ****** ****** *)
//
// primitive file reading functions
//

extern
fun{a:t@ype}
file_read (FILEref, &a? >> opt (a, r)): #[r:bool] bool (r)

typedef
file_read_type (a:t@ype) = (FILEref, &a? >> opt (a, r)) -> #[r:bool] bool (r)

extern
fun{a,b:t@ype}
file_read_tup2 (FILEref, &a? >> opt (a, r), &b? >> opt (b, r)): #[r:bool] bool (r)
extern
fun{a,b,c:t@ype}
file_read_tup3 (FILEref, &a? >> opt (a, r), &b? >> opt (b, r), &c? >> opt (c, r)): #[r:bool] bool (r)
extern
fun{a,b,c,d:t@ype}
file_read_tup4 (FILEref, &a? >> opt (a, r), &b? >> opt (b, r), &c? >> opt (c, r), &d? >> opt (d, r)): #[r:bool] bool (r)
extern
fun{a,b,c,d,e:t@ype}
file_read_tup5 (FILEref, &a? >> opt (a, r), &b? >> opt (b, r), &c? >> opt (c, r), &d? >> opt (d, r), &e? >> opt (e, r)): #[r:bool] bool (r)
extern
fun{a,b,c,d,e,f:t@ype}
file_read_tup6 (FILEref, &a? >> opt (a, r), &b? >> opt (b, r), &c? >> opt (c, r), &d? >> opt (d, r), &e? >> opt (e, r), &f? >> opt (f, r)): #[r:bool] bool (r)
extern
fun{a,b,c,d,e,f,g:t@ype}
file_read_tup7 (
  FILEref
, &a? >> opt (a, r), &b? >> opt (b, r), &c? >> opt (c, r), &d? >> opt (d, r), &e? >> opt (e, r)
, &f? >> opt (f, r), &g? >> opt (g, r)
): #[r:bool] bool (r)
extern
fun{a,b,c,d,e,f,g,h:t@ype}
file_read_tup8 (
  FILEref
, &a? >> opt (a, r), &b? >> opt (b, r), &c? >> opt (c, r), &d? >> opt (d, r), &e? >> opt (e, r)
, &f? >> opt (f, r), &g? >> opt (g, r), &h? >> opt (h, r)
): #[r:bool] bool (r)

implement{a,b}
file_read_tup2 (fp, a, b) = let
  val ar = file_read<a> (fp, a) in
  if ar then let
    val br = file_read<b> (fp, b) in
    if br then true
    else let
      prval () = opt_reset_mac (a) in
      false
    end
  end else let
    prval () = opt_none {b} (b) in
    false
  end
end // end of [file_read_tup2]

implement{a,b,c}
file_read_tup3 (fp, a, b, c) = let
  val abr = file_read_tup2<a,b> (fp, a, b) in
  if abr then let
    val cr = file_read<c> (fp, c) in
    if cr then true
    else let
      prval () = opt_reset_mac (a, b) in
      false
    end
  end else let
    prval () = opt_none {c} (c) in
    false
  end
end // end of [file_read_tup3]

implement{a,b,c,d}
file_read_tup4 (fp, a, b, c, d) = let
  val abcr = file_read_tup3<a,b,c> (fp, a, b, c) in
  if abcr then let
    val dr = file_read<d> (fp, d) in
    if dr then true
    else let
      prval () = opt_reset_mac (a, b, c) in
      false
    end
  end else let
    prval () = opt_none {d} (d) in
    false
  end
end // end of [file_read_tup4]

implement{a,b,c,d,e}
file_read_tup5 (fp, a, b, c, d, e) = let
  val abcdr = file_read_tup4<a,b,c,d> (fp, a, b, c, d) in
  if abcdr then let
    val er = file_read<e> (fp, e) in
    if er then true
    else let
      prval () = opt_reset_mac (a, b, c, d) in
      false
    end
  end else let
    prval () = opt_none {e} (e) in
    false
  end
end // end of [file_read_tup5]

implement{a,b,c,d,e,f}
file_read_tup6 (fp, a, b, c, d, e, f) = let
  val abcder = file_read_tup5<a,b,c,d,e> (fp, a, b, c, d, e) in
  if abcder then let
    val fr = file_read<f> (fp, f) in
    if fr then true
    else let
      prval () = opt_reset_mac (a, b, c, d, e) in
      false
    end
  end else let
    prval () = opt_none {f} (f) in
    false
  end
end // end of [file_read_tup6]

implement{a,b,c,d,e,f,g}
file_read_tup7 (fp, a, b, c, d, e, f, g) = let
  val abcdefr = file_read_tup6<a,b,c,d,e,f> (fp, a, b, c, d, e, f) in
  if abcdefr then let
    val gr = file_read<g> (fp, g) in
    if gr then true
    else let
      prval () = opt_reset_mac (a, b, c, d, e, f) in
      false
    end
  end else let
    prval () = opt_none {g} (g) in
    false
  end
end // end of [file_read_tup7]

implement{a,b,c,d,e,f,g,h}
file_read_tup8 (fp, a, b, c, d, e, f, g, h) = let
  val abcdefgr = file_read_tup7<a,b,c,d,e,f,g> (fp, a, b, c, d, e, f, g) in
  if abcdefgr then let
    val hr = file_read<h> (fp, h) in
    if hr then true
    else let
      prval () = opt_reset_mac (a, b, c, d, e, f, g) in
      false
    end
  end else let
    prval () = opt_none {h} (h) in
    false
  end
end // end of [file_read_tup8]

(* ****** ****** *)

extern
fun
file_read_uint8_le : file_read_type (uint8)
extern
fun
file_read_uint16_le : file_read_type (uint16)
extern
fun
file_read_uint32_le : file_read_type (uint32)

implement
file_read_uint8_le (f, r) = let
  val res = $STDIO.fgetc(f)
in
  if res < 0 then let
    prval () = opt_none {uint8} (r)
  in
    false
  end else let
    val () = r := $UNSAFE.castvwtp0 {uint8} (res)
    prval () = opt_some {uint8} (r)
  in
    true
  end
end // end of [file_read_uint8_le]
//
implement
file_read_uint16_le (f, r) = let
  var r1: uint8
  and r2: uint8
  val b1 = file_read_uint8_le (f, r1)
in
  if :(r1: uint8?, r2: uint8?) => b1 then let
    val b2 = file_read_uint8_le (f, r2)
  in
    if :(r1: uint8?, r2: uint8?) => b2 then let
      val r1_ = $UNSAFE.castvwtp0{uint16} (opt_unsome_get<uint8> (r1))
      val r2_ = $UNSAFE.castvwtp0{uint16} (opt_unsome_get<uint8> (r2))
      val () = r := g0uint_lor_uint16 (g0uint_lsl_uint16 (r2_, 8), r1_)
      prval () = opt_some {uint16} (r)
    in
      true
    end else let
      prval () = opt_none {uint16} (r)
      prval () = opt_clear {uint8} (r1)
      prval () = opt_unnone {uint8} (r2)
    in
      false
    end
  end else let
    prval () = opt_none {uint16} (r)
    prval () = opt_unnone {uint8} (r1)
  in
    false
  end
end
//
implement
file_read_uint32_le (f, r) = let
  var r1: uint16
  and r2: uint16
  val b1 = file_read_uint16_le (f, r1)
in
  if :(r1: uint16?, r2: uint16?) => b1 then let
    val b2 = file_read_uint16_le (f, r2)
  in
    if :(r1: uint16?, r2: uint16?) => b2 then let
      val r1_ = $UNSAFE.castvwtp0{uint32} (opt_unsome_get<uint16> (r1))
      val r2_ = $UNSAFE.castvwtp0{uint32} (opt_unsome_get<uint16> (r2))
      val () = r := g0uint_lor_uint32 (g0uint_lsl_uint32 (r2_, 16), r1_)
      prval () = opt_some {uint32} (r)
    in
      true
    end else let
      prval () = opt_none {uint32} (r)
      prval () = opt_clear {uint16} (r1)
      prval () = opt_unnone {uint16} (r2)
    in
      false
    end
  end else let
    prval () = opt_none {uint32} (r)
    prval () = opt_unnone {uint16} (r1)
  in
    false
  end
end
//
(* ****** ****** *)

extern
fun{a:t@ype}
file_read_array$elt (
  FILEref
, &a? >> opt (a, r)
): #[r:bool] bool (r)

extern
fun{a:t@ype}
file_read_array_lr {n:int} ( // left to right
  FILEref
, &(@[a?][n]) >> opt (@[a][n], r)
, size_t n
) : #[r:bool] bool (r)

extern
fun{a:t@ype}
file_read_array_rl {n:int} ( // right to left
  FILEref
, &(@[a?][n]) >> opt (@[a][n], r)
, size_t n
) : #[r:bool] bool (r)

implement{a}
file_read_array$elt (fp, x) = file_read<a> (fp, x)
//
implement{a}
file_read_array_lr {n} (fp, A, asz) = let
//
fun
aux {i,n:nat | i <= n} {l:addr} (
  pf1_arr: array_v (a, l, i), pf2_arr: array_v (a?, l+i*sizeof(a), n-i)
| p_arr: ptr (l+i*sizeof(a)), i: size_t i, n: size_t n
): [r:int] (vor (array_v (a, l, n), array_v (a?, l, n), r) | int r) = (
  if i < n then let
    prval (pf_at, pf2_arr) = array_v_uncons {a?} (pf2_arr)
    prval [l0:addr] EQADDR () = ptr_get_index (p_arr)
    val p_at = p_arr : ptr l0
    prval pf_at = pf_at : a? @ l0
    val res = file_read_array$elt<a> (fp, !p_at)
  in
    if res then let
      prval () = opt_unsome {a} (!p_at)
      prval pf1_arr = array_v_extend {a} (pf1_arr, pf_at)
      val p1_arr = ptr1_succ<a> (p_arr)
    in
      aux (pf1_arr, pf2_arr | p1_arr, succ(i), n)
    end else let
      prval p_bas = praxi_ptr {l} ()
      prval () = opt_unnone {a} (!p_at)
      prval () = topize {@[a][i]} (!p_bas)
      prval pf2_arr = array_v_cons {a?} (pf_at, pf2_arr)
      prval pf_res = array_v_unsplit {a?} (pf1_arr, pf2_arr)
    in
      #[.. | (VORright (pf_res) | 1)]
    end
  end else let
    prval () = array_v_unnil {a?} (pf2_arr)
    prval pf_res = pf1_arr
  in
    #[.. | (VORleft (pf_res) | 0)]
  end // end of [if]
) (* end of [aux] *)
//
prval pf1_arr = array_v_nil {a} ()
prval pf2_arr = view@(A)
val p_arr = addr@(A)
prval [l:addr] EQADDR () = eqaddr_make_ptr (p_arr)
prval () = lemma_g1uint_param (asz)
val (pf_vor | r) = aux {0,n} {l} (pf1_arr, pf2_arr |  p_arr, (i2sz)0, asz)
//
in
//
if r = 0 then let
  prval VORleft pf_arr = pf_vor
  prval () = view@A := pf_arr
  prval () = opt_some {@[a][n]} (A)
in
  true
end else let
  prval VORright pf_arr = pf_vor
  prval () = view@A := pf_arr
  prval () = opt_none {@[a][n]} (A)
in
  false
end // end of [if]
//
end // end of [file_read_array_lr]
//
implement{a}
file_read_array_rl {n} (fp, A, asz) = let
//
fun
aux {i,n:nat | i <= n} {l:addr} (
  pf1_arr: array_v (a?, l, i), pf2_arr: array_v (a, l+i*sizeof(a), n-i)
| p_arr: ptr (l+i*sizeof(a)), i: size_t i, n: size_t n
): [r:int] (vor (array_v (a, l, n), array_v (a?, l, n), r) | int r) = (
  if i > 0 then let
    prval (pf1_arr, pf_at) = array_v_unextend {a?} (pf1_arr)
    val p1_arr = ptr1_pred<a> (p_arr)
    prval [l0:addr] EQADDR () = ptr_get_index (p1_arr)
    val p_at = p1_arr : ptr l0
    prval pf_at = pf_at : a? @ l0
    val res = file_read_array$elt<a> (fp, !p_at)
  in
    if res then let
      prval () = opt_unsome {a} (!p_at)
      prval pf2_arr = array_v_cons {a}{l0} (pf_at, pf2_arr)
    in
      aux (pf1_arr, pf2_arr | p1_arr, pred(i), n)
    end else let
      prval p_bas = praxi_ptr {l} ()
      prval () = opt_unnone {a} (!p_at)
      prval pf1_arr = array_v_extend {a?} (pf1_arr, pf_at)
      prval pf_res = array_v_unsplit {a?} (pf1_arr, pf2_arr)
    in
      #[.. | (VORright (pf_res) | 1)]
    end
  end else let
    prval () = array_v_unnil {a?} (pf1_arr)
    prval pf_res = pf2_arr
    prval MULbas () = mul_make {i,sizeof(a)} ()
  in
    #[.. | (VORleft (pf_res) | 0)]
  end // end of [if]
) (* end of [aux] *)
//
val p_arr = addr@(A)
prval [l0:addr] EQADDR () = eqaddr_make_ptr (p_arr)
val p_arr = ptr1_add_guint<a> (p_arr, asz)
prval [l:addr] EQADDR () = eqaddr_make_ptr (p_arr)
//
prval pf1_arr = view@(A)
prval pf2_arr = array_v_nil {a} ()
prval () = lemma_g1uint_param (asz)
val (pf_vor | r) = aux (pf1_arr, pf2_arr |  p_arr, asz, asz)
//
in
//
if r = 0 then let
  prval VORleft pf_arr = pf_vor
  prval () = view@A := pf_arr
  prval () = opt_some {@[a][n]} (A)
in
  true
end else let
  prval VORright pf_arr = pf_vor
  prval () = view@A := pf_arr
  prval () = opt_none {@[a][n]} (A)
in
  false
end // end of [if]
//
end // end of [file_read_array_rl]
//
(* ****** ****** *)

extern
fun{a:t@ype}
file_read_matrix_row {n:int} (
  FILEref
, &(@[a?][n]) >> opt (@[a][n], r)
, size_t n
): #[r:bool] bool (r)

extern
fun{a:t@ype}
file_read_matrix_td(*top-down*) {m,n:int} (
  FILEref
, &(@[a?][m*n]) >> opt (@[a][m*n], r)
, size_t m
, size_t n
) : #[r:bool] bool (r)
//
extern
fun{a:t@ype}
file_read_matrix_bu(*bottom-up*) {m,n:int} (
  FILEref
, &(@[a?][m*n]) >> opt (@[a][m*n], r)
, size_t m
, size_t n
) : #[r:bool] bool (r)
//
extern
praxi
lemma_array_sizeof {a:vt@ype} {n:nat} (): [sizeof(@[a][n]) == n*sizeof(a)] void
//
extern
praxi
lemma_array2_sizeof {a:vt@ype} {m,n:nat} (): [sizeof(@[a][m*n]) == m*n*sizeof(a)] void
//
implement{a}
file_read_matrix_row {n} (fp, A, asz) = file_read_array_lr<a> (fp, A, asz)
//
implement{a}
file_read_matrix_td {m,n} (fp, mat, m, n) = let
//
typedef T = @[a][n]
prval () = lemma_g1uint_param (n)
//
fun
aux {i,m:nat | i <= m} {l:addr} (
  pf1_arr: array_v (T, l, i), pf2_arr: array_v (T?, l+i*sizeof(T), m-i)
| p_arr: ptr (l+i*sizeof(T)), i: size_t i, m: size_t m
): [r:int] (vor (array_v (T, l, m), array_v (T?, l, m), r) | int r) = (
  if i < m then let
    prval (pf_at, pf2_arr) = array_v_uncons {T?} (pf2_arr)
    prval [l0:addr] EQADDR () = ptr_get_index (p_arr)
    val p_at = p_arr : ptr l0
    prval pf_at = pf_at : T? @ l0
    val res = file_read_matrix_row<a> (fp, !p_at, n)
  in
    if res then let
      prval () = opt_unsome {T} (!p_at)
      prval pf1_arr = array_v_extend {T} (pf1_arr, pf_at)
      val p1_arr = ptr1_add_guint<a> (p_arr, n)
      prval () = lemma_array_sizeof {a}{n} ()
    in
      aux (pf1_arr, pf2_arr | p1_arr, succ(i), m)
    end else let
      prval p_bas = praxi_ptr {l} ()
      prval () = opt_unnone {T} (!p_at)
      prval () = topize {@[T][i]} (!p_bas)
      prval pf2_arr = array_v_cons {T?} (pf_at, pf2_arr)
      prval pf_res = array_v_unsplit {T?} (pf1_arr, pf2_arr)
    in
      #[.. | (VORright (pf_res) | 1)]
    end
  end else let
    prval () = array_v_unnil {T?} (pf2_arr)
    prval pf_res = pf1_arr
  in
    #[.. | (VORleft (pf_res) | 0)]
  end // end of [if]
) (* end of [aux] *)
//
prval pf_arr = view@(mat)
prval pf_mat = array_v_group {a?} (pf_arr)
//
prval pf1_arr = array_v_nil {T} ()
prval pf2_arr = pf_mat
val p_arr = addr@(mat)
prval [l:addr] EQADDR () = eqaddr_make_ptr (p_arr)
prval () = lemma_g1uint_param (m)
val (pf_vor | r) = aux {0,m} {l} (pf1_arr, pf2_arr |  p_arr, (i2sz)0, m)
//
in
//
if r = 0 then let
  prval VORleft pf_arr = pf_vor
  prval () = view@(mat) := array_v_ungroup {a} (pf_arr)
  prval () = opt_some {@[a][m*n]} (mat)
in
  true
end else let
  prval VORright pf_arr = pf_vor
  prval () = view@(mat) := array_v_ungroup {a?} (pf_arr)
  prval () = opt_none {@[a][m*n]} (mat)
in
  false
end // end of [if]
//
end // end of [file_read_matrix_td]
//
implement{a}
file_read_matrix_bu {m,n} (fp, mat, m, n) = let
//
typedef T = @[a][n]
prval () = lemma_g1uint_param (n)
//
fun
aux {i,m:nat | i <= m} {l:addr} (
  pf1_arr: array_v (T?, l, i), pf2_arr: array_v (T, l+i*sizeof(T), m-i)
| p_arr: ptr (l+i*sizeof(T)), i: size_t i, m: size_t m
) : [r:int] (vor (array_v (T, l, m), array_v (T?, l, m), r) | int r) = (
  if i > 0 then let
    prval (pf1_arr, pf_at) = array_v_unextend {T?} (pf1_arr)
    val p1_arr = ptr1_sub_guint<a> (p_arr, n)
    prval () = lemma_array_sizeof {a}{n} ()
    prval [l0:addr] EQADDR () = ptr_get_index (p1_arr)
    val p_at = p1_arr : ptr l0
    prval pf_at = pf_at : T? @ l0
    val res = file_read_matrix_row<a> (fp, !p_at, n)
  in
    if res then let
      prval () = opt_unsome {T} (!p_at)
      prval pf2_arr = array_v_cons {T}{l0} (pf_at, pf2_arr)
    in
      aux (pf1_arr, pf2_arr | p1_arr, pred(i), m)
    end else let
      prval p_bas = praxi_ptr {l} ()
      prval () = opt_unnone {T} (!p_at)
      prval pf1_arr = array_v_extend {T?} (pf1_arr, pf_at)
      prval pf_res = array_v_unsplit {T?} (pf1_arr, pf2_arr)
    in
      #[.. | (VORright (pf_res) | 1)]
    end
  end else let
    prval () = array_v_unnil {T?} (pf1_arr)
    prval pf_res = pf2_arr
    prval MULbas () = mul_make {i,sizeof(T)} ()
  in
    (VORleft (pf_res) | 0)
  end // end of [if]
) (* end of [aux] *)
//
val p_arr = addr@(mat)
prval [l0:addr] EQADDR () = eqaddr_make_ptr (p_arr)
prval () = lemma_g1uint_param (m)
prval () = lemma_g1uint_param (n)
val mn = m*n
prval pf_mul_mn = mul_make {m,n} ()
prval [mn:int] EQINT () = eqint_make_guint (mn)
prval () = mul_nat_nat_nat (pf_mul_mn)
prval () = mul_elim (pf_mul_mn)
val p_arr = ptr1_add_guint<a> (p_arr, mn)
prval () = lemma_array_sizeof {a?} {m} ()
prval () = lemma_array2_sizeof {a?} {m,n} ()
prval [l:addr] EQADDR () = eqaddr_make_ptr (p_arr)
prval () = __assert () where {
  extern
  prfun
  __assert (): [mn*sizeof(a?) == m*sizeof(@[a?][n])] void
} (* end of [prval] *)
//
prval pf_arr = view@(mat)
prval pf_mat = array_v_group {a?}{l0}{m,n} (pf_arr)
prval pf1_arr = pf_mat
prval pf2_arr = array_v_nil {T} ()
val (pf_vor | r) = aux (pf1_arr, pf2_arr |  p_arr, m, m)
//
in
//
if r = 0 then let
  prval VORleft pf_arr = pf_vor
  prval () = view@(mat) := array_v_ungroup (pf_arr)
  prval () = opt_some {@[a][m*n]} (mat)
in
  true
end else let
  prval VORright pf_arr = pf_vor
  prval () = view@(mat) := array_v_ungroup (pf_arr)
  prval () = opt_none {@[a][m*n]} (mat)
in
  false
end // end of [if]
//
end // end of [file_read_matrix_bu]
//
(* ****** ****** *)
// TGA image loading

local
//
extern
fun{a:t@ype}
row_read {n:int} (
  fp: FILEref
, A: &(@[a?][n]) >> opt (@[a][n], r)
, n: size_t n
) : #[r:bool] bool (r)
//
extern
fun{a:t@ype}
row_read_rle {n:int} (
  fp: FILEref
, A: &(@[a?][n]) >> opt (@[a][n], r)
, n: size_t n
) : #[r:bool] bool (r)
//
implement{a}
row_read {n} (fp, A, asz) = file_read_array_lr<a> (fp, A, asz)
//
implement{a}
row_read_rle {n} (fp, A, asz) = let
//
fun
row_read_cst {n:int} (
  A: &(@[a?][n]) >> @[a][n], asz: size_t n, x: a
): void = array_initize_elt<a> (A, asz, x)
//
fun loop {i,n:nat | i <= n} {l:addr} .<n-i>. (
  pf1_arr: array_v (a, l, i)
, pf2_arr: array_v (a?, l+i*sizeof(a), n-i)
| p1: ptr l
, p2: ptr (l+i*sizeof(a))
, m: size_t (n-i)
) : [r:int] (vor (array_v (a, l, n), array_v (a?, l, n), r) | int r) =
if m = 0 then let
  prval () = array_v_unnil {a?} (pf2_arr)
  prval pf_res = VORleft (pf1_arr)
in
  (pf_res | 0)
end else let
  prval p_bas = praxi_ptr {l} ()
  var hd: uint8
  val b_hd = file_read<uint8> (fp, hd)
in
  if :(hd: uint8?) => b_hd then let
    val hd = opt_unsome_get<uint8> (hd)
    val hd = g0uint2uint_uint8_uint (hd)
    val sz = (u2sz)((g1ofg0)((hd land (g0ofg1)0x7fu)))
    val sz = (g1ofg0)sz
    val sz = sz + (i2sz)1
    prval [j:int] EQINT () = eqint_make_guint (sz)
    val x = (hd land 0x80u) > 0u
  in
    if sz > m then let
      val () = prerrln!("[row_read_rle]: spans rows")
      prval () = topize {@[a][i]} (!p_bas)
      prval pf_arr = array_v_unsplit {a?} (pf1_arr, pf2_arr)
      prval pf_res = VORright (pf_arr)
    in
      (pf_res | 1)
    end else let // sz <= m
      prval (pf31_arr, pf32_arr) = array_v_split_at {a?} (pf2_arr | sz)
      prval [l0:addr] EQADDR () = ptr_get_index (p2)
      val p_arr = p2 : ptr l0
      prval pf31_arr = pf31_arr : array_v (a?, l0, j)
    in
      if x then let
        var v: a
        val bv = file_read<a> (fp, v)
      in
        if :(v: a?) => bv then let
          val v = opt_unsome_get<a> (v)
          val () = row_read_cst (!p_arr, sz, v)
          val p2 = ptr1_add_guint<a> (p_arr, sz)
          prval pf_arr = array_v_unsplit {a} (pf1_arr, pf31_arr)
          prval () = lemma_g1uint_param (sz)
          val m1 = m - sz
        in
          loop (pf_arr, pf32_arr | p1, p2, m1)
        end else let
          prval () = opt_unnone {a} (v)
          prval pf2_arr = array_v_unsplit (pf31_arr, pf32_arr)
          prval () = topize (!p_bas)
          prval pf_arr = array_v_unsplit (pf1_arr, pf2_arr)
        in
          (VORright (pf_arr) | 1)
        end
      end else let
        val br = row_read (fp, !p_arr, sz)
      in
        if br then let
          prval () = opt_unsome (!p_arr)
          val p2 = ptr1_add_guint<a> (p2, sz)
          prval pf_arr = array_v_unsplit {a} (pf1_arr, pf31_arr)
          val m = m - sz
        in
          loop (pf_arr, pf32_arr | p1, p2, m)
        end else let
          prval () = opt_unnone (!p_arr)
          prval pf3_arr = array_v_unsplit {a?} (pf31_arr, pf32_arr)
          prval () = topize (!p_bas)
          prval pf_arr = array_v_unsplit {a?} (pf1_arr, pf3_arr)
          prval pf_res = VORright (pf_arr)
        in
          (pf_res | 1)
        end
      end
    end
  end else let
    prval () = opt_unnone {uint8} (hd)
    prval () = topize {@[a][i]} (!p_bas)
    prval pf_res = array_v_unsplit {a?} (pf1_arr, pf2_arr)
  in
      #[.. | (VORright (pf_res) | 1)]
  end
end // end of [loop]
//
prval pf1_arr = array_v_nil {a} ()
val p_arr = addr@(A)
prval pf2_arr = view@(A)
prval () = lemma_g1uint_param (asz)
val (pf_res | res) = loop (pf1_arr, pf2_arr | p_arr, p_arr, asz)
//
in
  if res = 0 then let
    prval VORleft pf_arr = pf_res
    prval () = view@(A) := pf_arr
    prval () = opt_some {@[a][n]} (A)
  in
    true
  end else let
    prval VORright pf_arr = pf_res
    prval () = view@(A) := pf_arr
    prval () = opt_none {@[a][n]} (A)
  in
    false
  end
end // end of [row_read_rle]
//
in // of [local]
//
extern
fun
load_TGA {i,j:int;l0:addr} (
  FILEref
, &size_t(i)? >> opt (size_t w, r)
, &size_t(j)? >> opt (size_t h, r)
, &ptr(l0)? >> opt (ptr l, r)
) : #[w,h:int;l:addr;r:bool] (option_v ((matrix_v (uint32, l, w, h), mfree_gc_v (l)), r) | bool (r))
//
implement
file_read<uint8> (fp, x) = file_read_uint8_le (fp, x)
implement
file_read<uint16> (fp, x) = file_read_uint16_le (fp, x)
implement
file_read<uint32> (fp, x) = file_read_uint32_le (fp, x)
//
typedef TGA_hdr = @{
  id_len= uint8
, color_map_type= uint8
, image_type= uint8
, color_map_index= uint16
, color_map_length= uint16
, color_map_size= uint8
, origin_x= uint16
, origin_y= uint16
, width= uint16
, height= uint16
, pixel_size= uint8
, attribs= uint8
}
//
implement
file_read<TGA_hdr> (fp, res) = let
  val b1 = file_read_tup8<uint8,uint8,uint8,uint16,uint16,uint8,uint16,uint16> (
    fp
  , res.id_len, res.color_map_type
  , res.image_type
  , res.color_map_index, res.color_map_length, res.color_map_size
  , res.origin_x, res.origin_y
  )
in
  if b1 then let
    val b2 = file_read_tup4<uint16,uint16,uint8,uint8> (fp, res.width, res.height, res.pixel_size, res.attribs)
  in
    if b2 then let
      prval () = opt_unsome (res.id_len)
      // skip comment
      val id_len = g0uint2uint_uint8_uint (res.id_len)
      val id_len = g0uint2int_uint_lint (id_len)
      val b3 = $STDIO.fseek0 (fp, id_len, $STDIO.SEEK_CUR)
    in
      if b3 = 0 then let
        prval () = opt_unsome_mac (
          res.color_map_type, res.image_type, res.color_map_index, res.color_map_length, res.color_map_size
        , res.origin_x, res.origin_y, res.width, res.height, res.pixel_size, res.attribs
        ) (* end of [prval] *)
        prval () = opt_some {TGA_hdr} (res)        
      in
        true
      end else let
        prval () = topize (res.id_len)
        prval () = opt_clear_mac (
          res.color_map_type, res.image_type, res.color_map_index, res.color_map_length, res.color_map_size
        , res.origin_x, res.origin_y, res.width, res.height, res.pixel_size, res.attribs
        ) (* end of [prval] *)
        prval () = opt_none {TGA_hdr} (res)
      in
        false
      end
    end else let
      prval () = opt_clear_mac (
        res.id_len
      , res.color_map_type, res.image_type, res.color_map_index, res.color_map_length, res.color_map_size
      , res.origin_x, res.origin_y, res.width, res.height, res.pixel_size, res.attribs
      ) (* end of [prval] *)
      prval () = opt_none {TGA_hdr} (res)
    in
      false
    end
  end else let
    prval () = opt_clear_mac (
      res.id_len, res.color_map_type, res.image_type, res.color_map_index, res.color_map_length, res.color_map_size
    , res.origin_x, res.origin_y
    ) (* end of [prval] *)
    prval () = opt_none {TGA_hdr} (res)
  in
    false
  end
end // end of [file_read<TGA_hdr>]
//
extern
fun
file_read_grayscale : file_read_type (uint32)
extern
fun
file_read_rgb : file_read_type (uint32)
extern
fun
file_read_rgba : file_read_type (uint32)
//
overload lsl with g0uint_lsl_uint32
//
implement
file_read_grayscale (fp, res) = let
  var b: uint8
  val xb = file_read<uint8> (fp, b)
in
  if :(b: uint8?) => xb then let
    val b = $UNSAFE.castvwtp0{uint32} (opt_unsome_get<uint8> (b))
    val () = res := (($UNSAFE.castvwtp0{uint32}(255u) lsl 24) lor (b lsl 16) lor (b lsl 8) lor b)
    prval () = opt_some (res)
  in
    true
  end else let
    prval () = opt_clear (b)
    prval () = opt_none (res)
  in
    false
  end
end // end of [file_read_grayscale]
//
implement
file_read_rgb (fp, res) = let
  var b: uint8
  var g: uint8
  var r: uint8
  val bgr = file_read_tup3<uint8,uint8,uint8> (fp, b, g, r)
in
  if :(b: uint8?, g: uint8?, r: uint8?) => bgr then let
    val b = $UNSAFE.castvwtp0{uint32} (opt_unsome_get<uint8> (b))
    val g = $UNSAFE.castvwtp0{uint32} (opt_unsome_get<uint8> (g))
    val r = $UNSAFE.castvwtp0{uint32} (opt_unsome_get<uint8> (r))
    val () = res := (($UNSAFE.castvwtp0{uint32}(255u) lsl 24) lor (b lsl 16) lor (g lsl 8) lor r)
    prval () = opt_some (res)
  in
    true
  end else let
    prval () = opt_clear_mac (b, g, r)
    prval () = opt_none (res)
  in
    false
  end
end // end of [file_read_rgb]
//
implement
file_read_rgba (fp, res) = let
  var b: uint8
  and g: uint8
  and r: uint8
  and a: uint8
  val bgra = file_read_tup4<uint8,uint8,uint8,uint8> (fp, b, g, r, a)
in
  if :(b: uint8?, g: uint8?, r: uint8?, a: uint8?) => bgra then let
    val b = $UNSAFE.castvwtp0{uint32} (opt_unsome_get<uint8> (b))
    val g = $UNSAFE.castvwtp0{uint32} (opt_unsome_get<uint8> (g))
    val r = $UNSAFE.castvwtp0{uint32} (opt_unsome_get<uint8> (r))
    val a = $UNSAFE.castvwtp0{uint32} (opt_unsome_get<uint8> (a))
    val () = res := ((a lsl 24) lor (b lsl 16) lor (g lsl 8) lor r)
    prval () = opt_some (res)
  in
    true
  end else let
    prval () = opt_clear_mac (b, g, r, a)
    prval () = opt_none (res)
  in
    false
  end // end of [if]
end // end of [file_read_rgba]
//
extern
fun
file_read_TGA_image {m,n:int} {i:pos | i <= 4} (
  FILEref
, int(i)(*pixelsize, bytes*)
, bool(*rle*)
, bool(*topdown*)
, size_t m
, size_t n
, &(@[uint32?][m*n]) >> opt (@[uint32][m*n], r)): #[r:bool] bool (r)
//
implement
file_read_TGA_image {m,n} (fp, ps, rle, td, width, height, res) = (
//
case+ ps of
| 1 => let
//
  implement
  file_read_array$elt<uint32> (fp, x) = file_read_grayscale (fp, x)
in
  if rle then let
    implement
    file_read_matrix_row<uint32> (fp, A, asz) = row_read_rle<uint32> (fp, A, asz)
  in
    if td then file_read_matrix_td<uint32> (fp, res, width, height)
    else file_read_matrix_bu<uint32> (fp, res, width, height)
  end else let
    implement
    file_read_matrix_row<uint32> {n} (fp, A, asz) = row_read<uint32> (fp, A, asz)
  in
    if td then file_read_matrix_td<uint32> (fp, res, width, height)
    else file_read_matrix_bu<uint32> (fp, res, width, height)
  end // end of [if]
end // end of [let]
//
| 3 => let
//
  implement
  file_read_array$elt<uint32> (fp, x) = file_read_rgb (fp, x)
in
  if rle then let
    implement
    file_read_matrix_row<uint32> {n} (fp, A, asz) = row_read_rle<uint32> (fp, A, asz)
  in
    if td then file_read_matrix_td<uint32> (fp, res, width, height)
    else file_read_matrix_bu<uint32> (fp, res, width, height)
  end else let
    implement
    file_read_matrix_row<uint32> {n} (fp, A, asz) = row_read<uint32> (fp, A, asz)
  in
    if td then file_read_matrix_td<uint32> (fp, res, width, height)
    else file_read_matrix_bu<uint32> (fp, res, width, height)
  end // end of [if]
end // end of [let]
//
| 4 => let
//
  implement
  file_read_array$elt<uint32> (fp, x) = file_read_rgba (fp, x)
in
  if rle then let
    implement
    file_read_matrix_row<uint32> {n} (fp, A, asz) = row_read_rle<uint32> (fp, A, asz)
  in
    if td then file_read_matrix_td<uint32> (fp, res, width, height)
    else file_read_matrix_bu<uint32> (fp, res, width, height)
  end else let
    implement
    file_read_matrix_row<uint32> {n} (fp, A, asz) = row_read<uint32> (fp, A, asz)
  in
    if td then file_read_matrix_td<uint32> (fp, res, width, height)
    else file_read_matrix_bu<uint32> (fp, res, width, height)
  end // end of [if]
end // end of [let]
//
| _ => let
  prval () = opt_none (res)
  val () = println!("[image_input]: illegal pixel size ", ps)
in
  false
end // end of [let]
//
) (* end of [file_read_TGA_image] *)
//
implement
load_TGA
(fp, w, h, p) = let
  var hdr: TGA_hdr
  val b = file_read<TGA_hdr> (fp, hdr)
in
  if :(hdr: TGA_hdr?) => b then let
    prval () = opt_unsome (hdr)
  in
    if g0uint_isneqz_uint8 (hdr.color_map_type) then let
      val () = println!("[image_input]: color-mapped TGA images not supported")
      prval () = opt_none (w)
      prval () = opt_none (h)
      prval () = opt_none (p)
    in
      (None_v () | false)
    end else let
      val imt = g0uint2int_uint8_int (hdr.image_type)
    in
      if imt <> 2 andalso imt <> 3 andalso imt <> 10 andalso imt <> 11 then let
        val () = println!("[image_input]: only type 2 (RGB), 3 (grayscale), 10 (RGB RLE), 11 (grayscale RLE) TGA images are supported")
        prval () = opt_none (w)
        prval () = opt_none (h)
        prval () = opt_none (p)
      in
        (None_v () | false)
      end else let
        val rle = (imt = 10) || (imt = 11)
        val width = g0uint2uint_uint16_uint (hdr.width)
        val width = (g1ofg0)width
        val width = (u2sz)width
        val height = g0uint2uint_uint16_uint (hdr.height)
        val height = (g1ofg0)height
        val height = (u2sz)height
        prval [m:int] EQINT () = eqint_make_guint (width)
        prval [n:int] EQINT () = eqint_make_guint (height)
        prval () = lemma_g1uint_param (width)
        prval () = lemma_g1uint_param (height)
      in
        if g1uint_iseqz(width) || g1uint_iseqz(height) then let
          val () = println!("[image_input]: zero width or height!")
          prval () = opt_none_mac (w, h, p)
        in
          (None_v () | false)
        end else let
          val attribs = g0uint2uint_uint8_uint (hdr.attribs)
          val attribs = attribs land 0x20u
          val td = iseqz(attribs)
          val ps = hdr.pixel_size
          val ps = g0uint2int_uint8_int (ps)
          val psz = (g1ofg0)ps
          val sz2 = width * height
          val (pf_arr, pf_gc | p_arr) = array_ptr_alloc<uint32> (sz2)
          prval [l:addr] EQADDR () = eqaddr_make_ptr (p_arr)
          val b = (
          ) (* end of [val] *)
        in
          if implies (imt = 2 || imt = 10, ps = 32 || ps = 24) then let
            val psz = (if ps = 32 then 4 else 3): [i:int | i>0; i <= 4] int(i)
            val b = file_read_TGA_image (fp, psz, rle, td, width, height, !p_arr)
          in
            if b then let
              val () = w := width
              and () = h := height
              prval () = opt_some_mac (w, h)
              prval () = opt_unsome {@[uint32][m*n]} (!p_arr)
              prval pf_mat = array2matrix_v {uint32} (pf_arr)
              val () = p := p_arr
              prval () = opt_some {ptr(l)} (p)
            in
              (Some_v @(pf_mat, pf_gc) | true)
            end else let
              prval () = opt_none_mac (w, h, p)
              prval () = opt_unnone {@[uint32][m*n]} (!p_arr)
              val () = array_ptr_free {uint32} (pf_arr, pf_gc | p_arr)
            in
              (None_v () | false)
            end // end of [if]
          end else if implies (imt = 3 orelse imt = 11, ps = 8) then let
            val psz = 1
            val b = file_read_TGA_image (fp, psz, rle, td, width, height, !p_arr)
          in
            if b then let
              val () = w := width
              and () = h := height
              prval () = opt_some_mac (w, h)
              prval () = opt_unsome {@[uint32][m*n]} (!p_arr)
              prval pf_mat = array2matrix_v {uint32} (pf_arr)
              val () = p := p_arr
              prval () = opt_some {ptr(l)} (p)
            in
              (Some_v @(pf_mat, pf_gc) | true)
            end else let
              prval () = opt_none_mac (w, h, p)
              prval () = opt_unnone {@[uint32][m*n]} (!p_arr)
              val () = array_ptr_free {uint32} (pf_arr, pf_gc | p_arr)
            in
              (None_v () | false)
            end // end of [if]
          end else let
            prval () = opt_none_mac (w, h, p)
            val () = array_ptr_free {uint32} (pf_arr, pf_gc | p_arr)
          in
            (None_v () | false)
          end // end of [if]
        end // end of [if]
      end // end of [if]
    end // end of [if]
  end else let
    prval () = opt_unnone (hdr)
    prval () = opt_none_mac (w, h, p)
  in
    (None_v () | false)
  end // end of [if]
end // end of [load_TGA]
//
end // of [local]

(* ****** ****** *)

extern
fun
matrix_print_PPM {m,n:int} (FILEref, &matrix (uint32, m, n), size_t m, size_t n): void
implement
matrix_print_PPM {m,n} (fp, mat, m, n) = {
//
  val () = fprintln!(fp, "P3")
  val () = fprintln!(fp, "# generated by ATS/Postiats")
  val () = fprintln!(fp, m, " ", n)
  val () = fprintln!(fp, "255") // max color value
//
  implement
  fprint_matrix$sep1<> (out) = fprint!(out, " ")
  implement
  fprint_matrix$sep2<> (out) = fprintln!(out)
  implement
  fprint_ref<uint32> (out, x) = {
    val c = g0uint2uint_uint32_uint (x)
    val r = (c >> 0) land 0xFFu
    val g = (c >> 8) land 0xFFu
    val b = (c >> 16) land 0xFFu
    val () = fprint!(fp, r, " ", g, " ", b)
  }
  val () = fprint_matrix<uint32> (fp, mat, m, n)
//
}

(* ****** ****** *)

implement
main0 (argc, argv) = let
in
  if argc >= 2 then let
    val inp = fileref_open_exn (argv[1], file_mode_r)
    var w: size_t(0)
    var h: size_t(0)
    var p_mat: ptr(null)
    val (pf_res | res) = load_TGA (inp, w, h, p_mat)
  in
    if res then let
      prval Some_v @(pf_mat, pf_gc) = pf_res
      prval () = opt_unsome_mac (w, h, p_mat)
      prval [l:addr] EQADDR () = eqaddr_make_ptr (p_mat)
      prval [w:int] EQINT () = eqint_make_guint (w)
      prval [h:int] EQINT () = eqint_make_guint (h)
      val () = println!("open: success! width: ", w, ", height: ", h)
      //
      val () =
        if argc >= 3 then let
          val out = fileref_open_exn (argv[2], file_mode_w)      
          val () = matrix_print_PPM (out, !p_mat, w, h)
        in
          fileref_close (out)
        end // end of [if]
      //
      prval pf_arr = matrix2array_v {uint32}{l}{w,h} (pf_mat)
      prval () = topize {@[uint32][w*h]} (!p_mat)
      prval pf_mat = array2matrix_v {uint32?}{l}{w,h} (pf_arr)
      val () = matrix_ptr_free (pf_mat, pf_gc | p_mat)
      //
      val () = w := (i2sz)0
      val () = h := (i2sz)0
      val () = p_mat := the_null_ptr
      //
    in
      fileref_close (inp)
    end else let
      prval None_v () = pf_res
      prval () = opt_clear_mac (w, h, p_mat)
      val () = println!("open: failed")
      val () = w := (i2sz)0
      val () = h := (i2sz)0
      val () = p_mat := the_null_ptr
    in
      fileref_close (inp)
    end
  end else let
    val () = println!(
    "not enough arguments! usage: loadtga <tga file> [<ppm file>] (optionally specify where to save the converted data"
    ) (* end of [val] *)
  in
    // nothing
  end // end of [if]
end

