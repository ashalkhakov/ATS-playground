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
//
implement{env}
fundigraph_scc$beg (env) = ()
implement{env}
fundigraph_scc$node (v, env) = ()
implement{env}
fundigraph_scc$end (env) = ()
//
local
//
typedef
vertex_info = @{onstack=bool, index=int, lowlink= int}
//
in // in of [local]
//
implement{env}
fundigraph_scc {n} (dg, E) = let
  val Digraph (sz, aref) = dg
  
  typedef T = size_t

  #define UNDEFINED ~1

  var cur = 0 : int
  val p_cur = addr@(cur)
  prval [lc:addr] EQADDR () = eqaddr_make_ptr (p_cur)
  
  var stack = list_vt_nil {size_t} ()
  val p_stack = addr@stack
  prval [ls:addr] EQADDR () = eqaddr_make_ptr (p_stack)

  val (pf_vi, pf_vif | p_vi) = array_ptr_alloc<vertex_info> (sz)
  prval [l:addr] EQADDR () = eqaddr_make_ptr (p_vi)
  implement
  array_initize$init<vertex_info> (i, x) = {
    val () = x.onstack := false
    val () = x.index := UNDEFINED
    val () = x.lowlink := UNDEFINED
  } (* end of [array_initize$init] *)
  val () = array_initize<vertex_info> (!p_vi, sz)

  //
  vtypedef senv0 = env
  vtypedef senv1 = env //(array_v (vertex_info, l, n), int @ lc, List_vt(T) @ ls | env)
  viewdef V = (array_v (vertex_info, l, n), int @ lc, List_vt(T) @ ls)
  //
  extern
  castfn senv_to (senv0):<> senv1
  extern
  castfn senv_fro (senv1):<> senv0
  //

  fun
  strongconnect(pf: !V >> _ | v: sizeLt(n), env: &(senv1) >> _): void = let  
    // Set the depth index for v to the smallest unused index
    val curindex = !p_cur + 1
    val () = !p_vi.[v].index := curindex
    val () = !p_vi.[v].lowlink := curindex
    val () = !p_cur := curindex

    val () = !p_vi.[v].onstack := true
    prval () = lemma_list_vt_param (!p_stack)
    val () = !p_stack := list_vt_cons{size_t}((g0ofg1)v, !p_stack)
//
//    val () = println!("pushed: ", v)
//
    // Consider successors of v 
    fun
    aux (pf: !V >> _ | xs: List (size_t), env: &(senv1)): void =
      case+ xs of
      | list_nil () => ()
      | list_cons (w, xs) => let
        val w = $UN.cast{sizeLt(n)} (w)
      in
        if :(env: senv1) => !p_vi.[w].index = UNDEFINED then begin
          // Successor w has not yet been visited; recurse on it
          strongconnect (pf | w, env);
          !p_vi.[v].lowlink := min (!p_vi.[v].lowlink, !p_vi.[w].lowlink)
        end else if :(env: senv1) => !p_vi.[w].onstack then begin
          // Successor w is in stack S and hence in the current SCC
          !p_vi.[v].lowlink := min (!p_vi.[v].lowlink, !p_vi.[w].index)
        end;
        aux (pf | xs, env)
      end
//
    val xs = arrayref_get_at (aref, v)
    // FIXME: depends entirely on our use of funset_listord...
    val xs = $UN.castvwtp0{List(size_t)} (xs)
    val () = aux (pf | xs, env)
//
    fun aux0 (pf: !V >> _ | env: &senv1 >> _): void = let
      val- ~list_vt_cons (w, xs) = !p_stack
      val () = !p_stack := xs
      
//      val () = println!("popped: ", w, " vs ", v)
      
      val w = $UN.cast{sizeLt(n)} (w)
      var vr = array_get_at_guint (!p_vi, w)
      val () = vr.onstack := false
      val () = array_set_at_guint (!p_vi, w, vr)
      val () = fundigraph_scc$node<env> (w, env)
    in
      if w <> v then aux0 (pf | env)
    end
  in
    // If v is a root node, pop the stack and generate an SCC
    if !p_vi.[v].lowlink = !p_vi.[v].index then let
      val () = fundigraph_scc$beg<env> (env)
      val () = aux0 (pf | env)
      val () = fundigraph_scc$end<env> (env)
    in
    end
  end // end of [strongconnect]
//
  fun
  loop {i:nat | i <= n} (pf: !V >> _ | v: size_t i, env: &senv1): void =
    if :(env: senv1) => v < sz then let
    in
      if:(env: senv1) => !p_vi.[v].index = UNDEFINED then
        strongconnect(pf | v, env);
      loop (pf | succ(v), env)
    end // end of [loop]
  prval pf = (pf_vi, view@cur, view@stack)
  val () = loop (pf | (i2sz)0, E)
  prval () = $effmask_wrt (pf_vi := pf.0)
  prval () = $effmask_wrt (view@cur := pf.1)
  prval () = $effmask_wrt (view@stack := pf.2)
  
  val () = array_ptr_free {vertex_info} (pf_vi, pf_vif | p_vi)
  val- ~list_vt_nil () = !p_stack
in
end

end // end of [fundigraph_scc]

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

  // test strongly connected components
  var dg1 = fundigraph_make ((i2sz)5)

  val-false = fundigraph_insert_edge (dg1, (i2sz)1, (i2sz)0)
  val-false = fundigraph_insert_edge (dg1, (i2sz)0, (i2sz)2)
  val-false = fundigraph_insert_edge (dg1, (i2sz)2, (i2sz)1)
  val-false = fundigraph_insert_edge (dg1, (i2sz)0, (i2sz)3)
  val-false = fundigraph_insert_edge (dg1, (i2sz)3, (i2sz)4)

  val () = fprintln!(stdout_ref, "digraph: ", dg1)

  implement
  fundigraph_scc$beg<int> (e) = print!("component ", e, ": ")
  implement
  fundigraph_scc$node<int> (v, env) = print!(v, " ")
  implement
  fundigraph_scc$end<int> (env) = (print_newline(); env := succ(env))
  var env = 0 : int
  val () = println!("testing SCC:")
  val () = fundigraph_scc<int> (dg1, env)
}

