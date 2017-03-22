#include
"share/atspre_staload.hats"

prfun
opt_reset {a:t@ype} .< >. (x: !opt (a, true) >> opt (a, false)): void = {
  prval () = opt_clear (x)
  prval () = opt_none (x)
}

extern
fun{a:t@ype}
fileref_load_one (FILEref, &INV(a)? >> opt (a, r)): #[r:bool] bool (r)
overload load with fileref_load_one

extern
fun{a:t@ype}
fileref_load_array {n:int} (
  FILEref, size_t n, &(@[a?][n]) >> opt (@[a][n], r)
): #[r:bool] bool(r)
//
extern
fun{a,b:t@ype}
fileref_load_tup2 (FILEref, &a? >> opt (a, r), &b? >> opt (b, r)): #[r:bool] bool (r)
overload fileref_load_many with fileref_load_tup2

extern
fun{a,b,c:t@ype}
fileref_load_tup3 (FILEref, &a? >> opt (a, r), &b? >> opt (b, r), z: &c? >> opt (c, r)): #[r:bool] bool (r)
overload fileref_load_many with fileref_load_tup3

extern
fun{a,b,c,d:t@ype}
fileref_load_tup4 (
  FILEref
, &a? >> opt (a, r), &b? >> opt (b, r), z: &c? >> opt (c, r), w: &d? >> opt (d, r)
): #[r:bool] bool (r)
overload fileref_load_many with fileref_load_tup4

datatype skip_load_t0ype (a:t@ype) = SKIP (a)
typedef skip (a:t@ype) = skip_load_t0ype (a)

datatype cst_load_t0ype (a:t@ype) = CST (a) of a
typedef cst (a:t@ype) = cst_load_t0ype (a)

staload
_ = "prelude/DATS/filebas.dats"

implement{a}
fileref_load_one (s, x) = fileref_load<a> (s, x)

// fileref_load (FILEref, &a? >> opt (a, b)): #[b:bool] bool (b)
// fileref_load_cst (FILEref, &cst(a)): bool
// fileref_load_skip {a:t@ype} (FILEref, skip(a)): bool
(*implement(A)
fileref_load<cst(A)> (s, res) = let
  // but we assume that res should be initialized???
in
end // end of [fileref_load]
*)
implement(A)
fileref_load<skip(A)> (s, res) = let
  var x: A
  // TODO: more efficient skipping that involves no actual parsing?
  // - doable for binary files
  // - no substitute for text files
  val b = fileref_load<A> (s, x)
in
  if :(x: A?) => b then let
    prval () = opt_clear {A} (x)
    val () = res := SKIP {A} ()
    prval () = opt_some {skip(A)} (res)
  in
    true
  end else let
    prval () = opt_unnone {A} (x)
    prval () = opt_none {skip(A)} (res)
  in
    false
  end
end

implement{a}
fileref_load_array {n} (s, asz, A) = let
  fun
  aux0 {l:addr} (pf_at: !a? @ l >> opt (a, b) @ l | p: ptr l): #[b:bool] bool b =
    fileref_load<a> (s, !p)
  // end of [aux0]
  castfn
  aux1 {l:addr} .< >. (pf_at: !opt (a, true) @ l >> a @ l | p: ptr l):<> void = {
    prval () = opt_unsome (!p)
  } (* end of [aux1] *)
  castfn
  aux2 {l:addr} .< >. (pf_at: !opt (a, false) @ l >> a? @ l | p: ptr l):<> void = {
    prval () = opt_unnone (!p)
  } (* end of [aux1] *)
  fun
  aux {n1,n2:nat} {l:addr} (
    pf1_arr: array_v (a, l, n1)
  , pf2_arr: array_v (a?, l+n1*sizeof(a), n2)
  | p: ptr l
  , p2: ptr (l+n1*sizeof(a))
  , n2: int n2
  ): [i:int] (vor (array_v (a, l, n1+n2), array_v (a?, l, n1+n2), i) | int i) =
    if n2 = 0 then let
      prval () = array_v_unnil (pf2_arr)
      prval pf = VORleft (pf1_arr)
    in
      (pf | 0)
    end else let
      prval (pf_at, pf2_arr) = array_v_uncons {a?} (pf2_arr)
      val res = aux0 (pf_at | p2)
    in
      if res then let
        prval () = aux1 (pf_at | p2)
        val p2 = ptr1_succ<a> (p2)
        val n2 = n2-1
        prval pf1_arr = array_v_extend (pf1_arr, pf_at)
      in
        aux (pf1_arr, pf2_arr | p, p2, n2)
      end else let
        prval () = aux2 (pf_at | p2)
        prval pf2_arr = array_v_cons (pf_at, pf2_arr)
        prval () = topize (!p)
        prval pf_arr = array_v_unsplit (pf1_arr, pf2_arr)
        prval pf = VORright (pf_arr)
      in
        (pf | 1)
      end
    end
  // end of [aux]
  val p_a = addr@(A)
  prval pf_a = view@(A)
  prval pf_emp = array_v_nil {a} ()
  val (pf | res) = aux (pf_emp, pf_a | p_a, p_a, (sz2i)asz)
in
  if res = 0 then let
    prval VORleft (pf_arr) = pf
    prval () = view@(A) := pf_arr
    prval () = opt_some { @[a][n] } (A)
  in
    true
  end else let
    prval VORright (pf_arr) = pf
    prval () = view@(A) := pf_arr
    prval () = opt_none { @[a][n] } (A)
  in
    false
  end
end // end of [fileref_load_array]

implement{a,b}
fileref_load_tup2 (s, x, y) = let
  val b1 = fileref_load<a> (s, x)
in
  if b1 then let
    val b2 = fileref_load<b> (s, y)
  in
    if b2 then let
    in
      true
    end else let
      prval () = opt_reset (x)
    in
      false
    end
  end else let
    prval () = opt_none (y)
  in
    false
  end
end

implement{a,b,c}
fileref_load_tup3 (s, x, y, z) = let
  val b1 = fileref_load_tup2<a,b> (s, x, y)
in
  if b1 then let
    val b2 = fileref_load<c> (s, z)
  in
    if b2 then true
    else let
      prval () = opt_reset (x)
      prval () = opt_reset (y)
    in
      false
    end
  end else let
    prval () = opt_none (z)
  in
    false
  end
end

implement{a,b,c,d}
fileref_load_tup4 (s, x, y, z, w) = let
  val b1 = fileref_load_tup3<a,b,c> (s, x, y, z)
in
  if b1 then let
    val b2 = fileref_load<d> (s, w)
  in
    if b2 then true
    else let
      prval () = opt_reset (x)
      prval () = opt_reset (y)
      prval () = opt_reset (z)
    in
      false
    end
  end else let
    prval () = opt_none (w)
  in
    false
  end
end

//
local
//
macrodef
rec
reset
  (xs) =
(
//
if iscons! (xs) then `(let
  val () = opt_reset (,(car! xs))
in
  ,(reset (cdr! xs))
end)
else `() // end of [if]
//
) // end of [reset]
//
macrodef
rec
auxlist (s, xs, y) =
(
//
if iscons! (xs) then `(let
  val b = load (,(s), ,(car! xs))
in
  if b then ,(auxlist (s, cdr! xs, y))
  else let
    prval () = opt_none (b)
  in
    false
  end
end)
else y // end of [if]
//
) // end of [auxlist]

in (* in of [local] *)

macdef
load_mac (s, xs) =
,(
  if islist! (xs) then auxlist (s, xs, `(true)) else `(fileref_load (,(s), ,(xs)))
) // end of [load_mac]

end // end of [local]
//

// simply reading data from a text file into a record

typedef img = @{
  w= int
, s1= float
}

fun
test0 () = let
  var i: int
  var j: float
  val fp = fileref_open_exn ("./multiload.txt", file_mode_r)
  val res = load_mac (fp, i)
in
  if :(i: int?(*, j: float?*) => res then let
    prval () = opt_unsome {int} (i)
    //prval () = opt_unsome {float} (j)
    val () = fileref_close (fp)
  in
  end else let
    prval () = opt_unnone {int} (i)
    //prval () = opt_unnone {float} (j)
    val () = fileref_close (fp)
  in
  end
end

implement
main0 () = let
  typedef T = float
  #define NDIM 5
  typedef ARR_T = @[T][NDIM]
  implement
  fileref_load<ARR_T> (s, x) = fileref_load_array<T> (s, (i2sz)NDIM, x)

  var i: img
  var s: skip(int)
  var arr = @[T][NDIM]()
  val fp = fileref_open_exn ("./multiload.txt", file_mode_r)
  val res = fileref_load_many<int,skip(int),float,ARR_T> (fp, i.w, s, i.s1, arr)
in
  if :(i: img?, s: skip(int)?, arr: ARR_T?) => res then let
    prval () = opt_unsome {int} (i.w)
    prval () = opt_unsome {skip(int)} (s)
    prval () = opt_unsome {float} (i.s1)
    prval () = opt_unsome {ARR_T} (arr)
    val () = print!("read from input: w=", i.w, ", h=(skipped), s1=", i.s1, ", array=(")
    val () = fprint_array_size<T> (stdout_ref, arr, (i2sz)NDIM)
    val () = println!(")")
    prval () = topize {img} (i)
    prval () = topize {skip(int)} (s)
    prval () = topize {ARR_T} (arr)
    val () = fileref_close (fp)
  in
  end else let
    val () = println!("failed to read input!")
    prval () = opt_unnone {int} (i.w)
    prval () = opt_unnone {skip(int)} (s)
    prval () = opt_unnone {float} (i.s1)
    prval () = opt_unnone {ARR_T} (arr)
    val () = fileref_close (fp)
  in
  end
end
