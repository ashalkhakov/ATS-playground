#include "share/atspre_staload.hats"

staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload "libats/SATS/funset_listord.sats"
staload _(*anon*) = "libats/DATS/funset_listord.dats"

(* ****** ****** *)

staload "./fundigraph.sats"

datatype Digraph (int) = {n:nat} Digraph (n) of (size_t n, arrayref (set (size_t), n))

assume digraph_type (n:int) = Digraph (n)

implement{
} fundigraph_make {n} (n) = let
  val nil = funset_nil{size_t} ()
  val aref = arrayref_make_elt<set(size_t)> (n, nil)
  val res = Digraph (n, aref)
in
  res
end // end of [fundigraph_make]

implement{}
fundigraph_insert_edge {n,i,j} (dg, src, dst) = let
  val Digraph (sz, aref) = dg
  var adj = arrayref_get_at (aref, src)
  val dst = (g0ofg1)dst
  val ex = funset_insert<size_t> (adj, dst)
  val () = arrayref_set_at (aref, src, adj)
in
  ex
end // end of [fundigraph_insert_edge]

implement{}
fprint_fundigraph$sep (out: FILEref) = fprint! (out, "; ")
implement{}
fprint_fundigraph$edgeto (out: FILEref) = fprint!(out, "->")
implement
fprint_fundigraph (out, dg) = {
//
val Digraph (sz, aref) = dg
prval [n:int] EQINT () = eqint_make_guint (sz)
//  
implement
fprint_funset$sep<> (out) = fprint_fundigraph$sep<> (out)
//
implement(env)
array_iforeach$fwork<set(size_t)><env> (i, xs, env) = {
  val () =
    if i > (i2sz)0 then fprint_fundigraph$sep<> (out)
  // end of [val]
  val () = fprint!(out, "vertex ", i, " {")
  val () = fprint_funset<size_t> (out, xs)
  val () = fprint!(out, "}")
} (* end of [arrayref_foreach$fwork] *)
//
val _(*length*) = arrayref_iforeach<set(size_t)> (aref, sz)
//
} (* end of [fprint_fundigraph] *)

implement{env}
fundigraph_foreach_dfs$fwork (src, dst, env) = ()
implement{env}
fundigraph_foreach_dfs_from_env {n} (dg, root, env) = let
  val Digraph (sz, aref) = dg
  val (pf_vis, pf_visf | p_vis) = array_ptr_alloc<bool> (sz)
  prval [l:addr] EQADDR () = eqaddr_make_ptr (p_vis)
  val () = array_initize_elt<bool> (!p_vis, sz, false)
  
  typedef T = size_t
  
  fun
  aux {m:nat} (
    pf_vis: !array_v (bool, l, n) >> _
  | stack: list_vt (T, m)
  , env: &(env) >> _
  ): void =
    case+ :(pf_vis: array_v (bool, l, n), env: env) => stack of
    | ~list_vt_cons (x0, stack1) => let
      val x = $UN.cast{sizeLt(n)} (x0)
    in
      if :(pf_vis: array_v (bool, l, n), env: env) => ~(!p_vis.[x]) then let
        val () = array_set_at_guint (!p_vis, x, true)
        val () = fundigraph_foreach_dfs$fwork<env> ((g0ofg1)root, (g0ofg1)x, env)
        val xs = arrayref_get_at (aref, x)
        //
        vtypedef senv0 = ptr
        vtypedef senv1 = (array_v (bool, l, n) | List_vt(T))
        //
        extern
        castfn senv_to (senv0):<> senv1
        extern
        castfn senv_fro (senv1):<> senv0
        //
        implement
        funset_foreach$fwork<T><senv0> (dst, env) = let
          val (pf_arr | stack) = senv_to (env)
          val dst = $UN.cast{sizeLt(0)}(dst)
        in
          if :(env: senv0) => !p_vis.[dst] = false then let
            prval () = lemma_list_vt_param {T} (stack)
            val dst = (g0ofg1)dst
            val list = list_vt_cons (dst, stack)
            val () = env := senv_fro (@(pf_arr | list))
          in
            (*empty*)
          end else let
            val () = env := senv_fro (@(pf_arr | stack))
          in
          end
        end // end of [funset_foreach$fwork]
        //
        val senv = (pf_vis | stack1)
        var senv_ = senv_fro (senv)
        val () = funset_foreach_env<T><senv0> (xs, senv_)
        val senv = senv_to (senv_)
        prval () = pf_vis := senv.0
        val stack2 = senv.1
        prval () = lemma_list_vt_param (stack2)
      in
        aux (pf_vis | stack2, env)
      end else begin
        aux (pf_vis | stack1, env)
      end
    end // end of [let]
    | ~list_vt_nil () => ()
  // end of [aux]
  
  val stack = list_vt_sing (root)

  val () = aux (pf_vis | stack, env)  

  val () = array_ptr_free {bool} (pf_vis, pf_visf | p_vis)
in
end // end of [fundigraph_foreach_reachable]

implement
main0 () = {

  var dg = fundigraph_make ((i2sz)4)

  val-false = fundigraph_insert_edge (dg, (i2sz)0, (i2sz)1)
  val-false = fundigraph_insert_edge (dg, (i2sz)0, (i2sz)2)
  val-false = fundigraph_insert_edge (dg, (i2sz)1, (i2sz)2)
  val-false = fundigraph_insert_edge (dg, (i2sz)2, (i2sz)0)
  val-false = fundigraph_insert_edge (dg, (i2sz)2, (i2sz)3)
  val-false = fundigraph_insert_edge (dg, (i2sz)3, (i2sz)3)
  
  val () = fprintln!(stdout_ref, "digraph: ", dg)
  implement(env)
  fundigraph_foreach_dfs$fwork<env> (src, dst, e) = {
    val () = println!("started at: ", src, ", found: ", dst)
  } (* end of [fundigraph_foreach_dfs$fwork] *)
  var env: void
  val () = println!("testing DFS:")
  val () = fundigraph_foreach_dfs_from_env (dg, (i2sz)2, env)
  // should print: 2 0 1 3

  val () = println!("finished!")
}