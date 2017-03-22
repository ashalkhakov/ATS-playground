staload "./rgn.sats"

#define ATS_DYNLOADFLAG 0

(* ****** ****** *)
//
local
//
staload _ = "prelude/DATS/pointer.dats"
//
dataprop addr_p (addr, bool) =
  | addr_p_none (null, false)
  | {l:agz} addr_p_some (l, true)
//
assume rgnptr (a:t@ype, l0:addr, b:bool) = [l:addr] (
  addr_p (l, b),  option_p (vsubw_p (a @ l, RGN(l0)), l > null)
| ptr l
)
//
in // in of [local]
//
implement
rgnptr_make_some {a} {l,l0} (pf_vsub | p) = let
  prval () = __trustme () where {
    extern prfun
    __trustme (): [l>null] void
  } (* end of [prval] *)
in
  #[l | (addr_p_some (), Some_p (pf_vsub) | p)]
end // end of [rgnptr_make_some]
implement
rgnptr_make_none {a} {l0} () = (addr_p_none (), None_p () | the_null_ptr)
//
(*implement
rgnptr_takeout {a} {l0} (
  pf_rgn | r
) = let
  val (addr_p_some (), Some_p pf_vsub | p_r) = r
  prval pf = vsubw_elim (pf_vsub)
  prval (pf_at, fpf) = pf (pf_rgn)
in
  #[.. | ((pf_at, fpf) | p_r)]
end // end of [rgnptr_takeout]
*)
//
implement
rgnptr_is_some {a} {l0} {b} (r) =
  if ptr_is_null (r.2) then let
    prval addr_p_none () = r.0 in
    false
  end else let
    prval addr_p_some () = r.0 in
    true
  end // end of [rgnptr_is_some]
//
implement
rgnptr_is_none {a} {l0} {b} (r) =
  if ptr_is_null (r.2) then let
    prval addr_p_none () = r.0 in
    true
  end else let
    prval addr_p_some () = r.0 in
    false
  end // end of [rgnptr_is_none]
//
implement
eq_rgnptr_rgnptr {a} {l0} (r1, r2) = (r1.2 = r2.2)
implement
neq_rgnptr_rgnptr {a} {l0} (r1, r2) = (r1.2 <> r2.2)
//
end // end of [local]
