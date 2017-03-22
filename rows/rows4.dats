#include
"share/atspre_staload.hats"

absprop t0ype_eq (vt@ype, vt@ype)
extern praxi t0ype_eq_refl : {a:vt@ype} () -> t0ype_eq (a, a)
extern praxi t0ype_eq_symm : {a,b:vt@ype} t0ype_eq (a, b) -> t0ype_eq (b, a)
extern praxi t0ype_eq_trans : {a,b,c:vt@ype} (t0ype_eq (a, b), t0ype_eq (b, c)) -> t0ype_eq (a, c)

(* ****** ****** *)

datasort t0ypes = // abstract

stacst t0ypes_nil : () -> t0ypes
stacst t0ypes_cons : (t@ype, t0ypes) -> t0ypes

// map t0ypes to a type
absprop t0ypes_tp (t0ypes, t@ype)
extern praxi t0ypes_tp_nil : () -> t0ypes_tp (t0ypes_nil, @())
extern praxi t0ypes_tp_cons :
  {t:t@ype;t1:t@ype;ts:t0ypes} t0ypes_tp (ts, t1) -> t0ypes_tp (t0ypes_cons (t, ts), @(t, t1))

(* ****** ****** *)

sortdef lab = int // mostly abstract
datasort row = // abstract

(*
// if [lab] is abstract
stacst eq_lab_lab : (lab, lab) -> bool
stadef == = eq_lab_lab
extern praxi lab_eq_refl {l:lab} (): [l == l] void
extern praxi lab_eq_symm {l1,l2:lab | l1 == l2} (): [l2 == l1] void
extern praxi lab_eq_tran {l1,l2,l3:lab | l1 == l2; l2 == l3} (): [l1 == l3] void

stacst ne_lab_lab : (lab, lab) -> bool
stadef != = ne_lab_lab
*)

(* ****** ****** *)

stacst row_emp : row
stacst row_ext : (lab, t@ype, row) -> row
stacst row_constr : row -> t@ype

stadef emp = row_emp
stadef ext = row_ext

(* ****** ****** *)

absprop rowdisj (row, row) // holds iff r1 and r2 are disjoint, i.e. hold no labels in common

// how to build up disjunction proof?

extern praxi
rowdisj_emp : {r:row} () -> rowdisj (r, emp)
// what about extension?
(*
extern praxi
rowdisj_ext_l :
  {l:lab;t:t@ype;r1,r2:row}
  (rowdisj (r1, r2), rowdisj (ext (l, t, emp), r1)) -> rowdisj (ext (l, t, r1), r2)
extern praxi
rowdisj_ext_r :
  {l:lab;t:t@ype;r1,r2:row}
  (rowdisj (r1, r2)) -> rowdisj (r1, ext (l, t, r2))
*)

extern praxi
rowdisj_symm : {r1,r2:row} rowdisj (r1, r2) -> rowdisj (r2, r1)
extern praxi
rowdisj_trans : {r1,r2,r3:row} (rowdisj (r1, r2), rowdisj (r2, r3)) -> rowdisj (r1, r3)

(* ****** ****** *)

absprop rowtp (row, t0ypes) // maps row to a tuple
extern praxi
rowtp_nil (): rowtp (emp, t0ypes_nil)
extern praxi
rowtp_cons {l:lab;t:t@ype;r:row;ts:t0ypes}
  (rowdisj (ext (l, t, emp), r), rowtp (r, ts)): rowtp (ext (l, t, r), t0ypes_cons (t, ts))

(* ****** ****** *)

stadef lab01 : lab = 1
stadef lab02 : lab = 2
stadef lab03 : lab = 3
stadef lab04 : lab = 4

prval () = (): [lab01 != lab02] void
prval () = (): [lab01 != lab03] void
prval () = (): [lab01 != lab04] void

prval rowdisj_test01 = rowdisj_emp ()

(* ****** ****** *)

implement
main0 () = ()
