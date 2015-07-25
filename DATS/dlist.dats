(* ****** ****** *)

staload "../SATS/dlist.sats"

(* ****** ****** *)
//
implement{}
fprint_dlfcircular$sep (out) = fprint (out, ", ")
//
implement{}
fprint_dlfcircular {n} {l} (pf_dlfc | out, p) = let
//
fun
loop {n:nat} {lf:agz;lfn,lp,lr,lrn:addr} (
  pf_at: !dlnode_v (lf, lp, lfn)
, pf_fseg: !dlfseg_v (n, lfn, lf, lr, lrn)
| p: ptr lf
, prn: ptr lrn
, out: FILEref
) : void = let
//
val pn = dlnode_ptr_next (pf_at | p)
//
val () = fprint_dlnode_ptr (pf_at | out, p)
//
prval () = dlfseg_lemma3 (pf_fseg)
//
in
//
if pn = prn then let
  prval dlfseg_v_nil () = pf_fseg
  prval () = pf_fseg := dlfseg_v_nil ()
in
  (*void*)
end else let
  val () = fprint_dlfcircular$sep<> (out)
  prval dlfseg_v_cons (pf1_at, pf1_fseg) = pf_fseg
  prval () = dlnode_ptr_is_gtz (pf1_at)
  val () = loop (pf1_at, pf1_fseg | pn, prn, out)
  prval () = pf_fseg := dlfseg_v_cons (pf1_at, pf1_fseg)
in
  (*void*)
end
//
end // end of [loop]
//
in
//
if p = the_null_ptr then let
//
prval dlfcircular_v_none () = pf_dlfc
prval () = pf_dlfc := dlfcircular_v_none ()
//
in (*void*) end
else let
//
prval dlfcircular_v_some (pf_hd, pf_fseg) = pf_dlfc
val () = loop (pf_hd, pf_fseg | p, p, out)
prval () = pf_dlfc := dlfcircular_v_some (pf_hd, pf_fseg)
//
in (*void*) end // end of [if]
//
end // end of [fprint_dlfcircular]
//
implement{}
fprint_dlfcircular_sep {n} {l} (
  pf_dlfc
| out: FILEref
, p
, sep
) = let
//
implement
fprint_dlfcircular$sep<> (out) = fprint (out, sep)
//
in
  fprint_dlfcircular (pf_dlfc | out, p)
end // end of [fprint_dlfcircular_sep]
//
(* ****** ****** *)

implement
dlfcircular_ptr_length {n} {l} (pf_dlfc | p) = let
//
fun
loop {n,acc:nat} {lf:agz;lfn,lp,lr,lrn:addr} (
  pf_at: !dlnode_v (lf, lp, lfn)
, pf_fseg: !dlfseg_v (n, lfn, lf, lr, lrn)
| p: ptr lf
, prn: ptr lrn
, acc: int acc
) : int (acc+n) = let
//
val pn = dlnode_ptr_next (pf_at | p)
prval () = dlfseg_lemma3 (pf_fseg)
//
in
//
if pn = prn then let
  prval dlfseg_v_nil () = pf_fseg
  prval () = pf_fseg := dlfseg_v_nil ()
in
  acc
end else let
  prval dlfseg_v_cons (pf1_at, pf1_fseg) = pf_fseg
  prval () = dlnode_ptr_is_gtz (pf1_at)
  val res = loop (pf1_at, pf1_fseg | pn, prn, acc+1)
  prval () = pf_fseg := dlfseg_v_cons (pf1_at, pf1_fseg)
in
  res
end
//
end // end of [loop]
//
in
//
if p = the_null_ptr then let
//
prval dlfcircular_v_none () = pf_dlfc
prval () = pf_dlfc := dlfcircular_v_none ()
//
in 0 end
else let
//
prval dlfcircular_v_some (pf_hd, pf_fseg) = pf_dlfc
val res = loop (pf_hd, pf_fseg | p, p, 1)
prval () = pf_dlfc := dlfcircular_v_some (pf_hd, pf_fseg)
//
in res end // end of [if]
//
end // end of [dlfcircular_ptr_length]

(* ****** ****** *)

implement
dlfcircular_ptr_free {n} {l} (pf_dlfc | p) = let
//
fun
loop {n:nat} {lf:agz;lfn,lp,lr,lrn:addr} (
  pf_at: dlnode_v (lf, lp, lfn)
, pf_fseg: dlfseg_v (n, lfn, lf, lr, lrn)
| p: ptr lf
, prn: ptr lrn
) : void = let
//
val pn = dlnode_ptr_next (pf_at | p)
val () = dlnode_ptr_free (pf_at | p)
prval () = dlfseg_lemma3 (pf_fseg)
//
in
  if pn = prn then let
    prval dlfseg_v_nil () = pf_fseg
  in
    (*void*)
  end else let
    prval dlfseg_v_cons (pf1_at, pf1_fseg) = pf_fseg
    prval () = dlnode_ptr_is_gtz (pf1_at)
  in
    loop (pf1_at, pf1_fseg | pn, prn)
  end
end // end of [loop]
//
in
  if p = the_null_ptr then let
    prval dlfcircular_v_none () = pf_dlfc
  in (*void*) end else let
    prval dlfcircular_v_some (pf_hd, pf_fseg) = pf_dlfc
  in
    loop (pf_hd, pf_fseg | p, p)
  end // end of [if]
end // end of [dlfcircular_ptr_free]

