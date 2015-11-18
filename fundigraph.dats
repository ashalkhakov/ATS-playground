#include "share/atspre_staload.hats"

staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload "./fundigraph.sats"

datatype Digraph (int) = {n:nat} Digraph (n) of (size_t n, arrayref (List (size_t), n))

assume digraph_type (n:int) = Digraph (n)

implement{
} fundigraph_make {n} (n) = let
  val nil = list_nil{size_t} ()
  val aref = arrayref_make_elt<List(size_t)> (n, nil)
  val res = Digraph (n, aref)
in
  res
end // end of [fundigraph_make]

implement{}
fundigraph_insert_edge {n,i,j} (dg, src, dst) = let
  val Digraph (sz, aref) = dg
  var adj = arrayref_get_at (aref, src)
  val dst = (g0ofg1)dst
  // NOTE: we should be checking for duplicates here!
  prval () = lemma_list_param (adj)
  val adj = list_cons (dst, adj)
  val () = arrayref_set_at (aref, src, adj)
in
  (*empty*)
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
fprint_list$sep<> (out) = fprint_fundigraph$sep<> (out)
//
implement(env)
array_iforeach$fwork<List(size_t)><env> (i, xs, env) = {
  val () =
    if i > (i2sz)0 then fprint_fundigraph$sep<> (out)
  // end of [val]
  val () = fprint!(out, "vertex ", i, " {")
  val () = fprint_list<size_t> (out, xs)
  val () = fprint!(out, "}")
} (* end of [arrayref_foreach$fwork] *)
//
val _(*length*) = arrayref_iforeach<List(size_t)> (aref, sz)
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
        list_foreach$fwork<T><senv0> (dst, env) = let
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
        end // end of [list_foreach$fwork]
        //
        val senv = (pf_vis | stack1)
        var senv_ = senv_fro (senv)
        val () = list_foreach_env<T><senv0> (xs, senv_)
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
  viewdef V = (array_v (vertex_info, l, n), int @ lc, List_vt(T) @ ls)
  //

  fun
  strongconnect(pf: !V >> _ | v: sizeLt(n), env: &(env) >> _): void = let  
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
    aux (pf: !V >> _ | xs: List (size_t), env: &(env)): void =
      case+ xs of
      | list_nil () => ()
      | list_cons (w, xs) => let
        val w = $UN.cast{sizeLt(n)} (w)
      in
        if :(env: env) => !p_vi.[w].index = UNDEFINED then begin
          // Successor w has not yet been visited; recurse on it
          strongconnect (pf | w, env);
          !p_vi.[v].lowlink := min (!p_vi.[v].lowlink, !p_vi.[w].lowlink)
        end else if :(env: env) => !p_vi.[w].onstack then begin
          // Successor w is in stack S and hence in the current SCC
          !p_vi.[v].lowlink := min (!p_vi.[v].lowlink, !p_vi.[w].index)
        end;
        aux (pf | xs, env)
      end
//
    val xs = arrayref_get_at (aref, v)
    val () = aux (pf | xs, env)
//
    fun aux0 (pf: !V >> _ | env: &env >> _): void = let
      val- ~list_vt_cons (w, xs) = !p_stack
      val () = !p_stack := xs
      
//      val () = println!("popped: ", w, " vs ", v)
      
      val w = $UN.cast{sizeLt(n)} (w)
      var vr = array_get_at_guint (!p_vi, w)
      val () = vr.onstack := false
      val () = array_set_at_guint (!p_vi, w, vr)

//      val () = println!("calling [node]:")

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
  loop {i:nat | i <= n} (pf: !V >> _ | v: size_t i, env: &(env) >> _): void =
    if :(env: env) => v < sz then let
    in
      if:(env: env) => !p_vi.[v].index = UNDEFINED then
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

  val () = fundigraph_insert_edge (dg, (i2sz)0, (i2sz)1)
  val () = fundigraph_insert_edge (dg, (i2sz)0, (i2sz)2)
  val () = fundigraph_insert_edge (dg, (i2sz)1, (i2sz)2)
  val () = fundigraph_insert_edge (dg, (i2sz)2, (i2sz)0)
  val () = fundigraph_insert_edge (dg, (i2sz)2, (i2sz)3)
  val () = fundigraph_insert_edge (dg, (i2sz)3, (i2sz)3)
  
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

  val () = fundigraph_insert_edge (dg1, (i2sz)1, (i2sz)0)
  val () = fundigraph_insert_edge (dg1, (i2sz)0, (i2sz)2)
  val () = fundigraph_insert_edge (dg1, (i2sz)2, (i2sz)1)
  val () = fundigraph_insert_edge (dg1, (i2sz)0, (i2sz)3)
  val () = fundigraph_insert_edge (dg1, (i2sz)3, (i2sz)4)

  val () = fprintln!(stdout_ref, "digraph: ", dg1)

  absvt@ype E = @{sz=size_t, p=ptr, ncomp=int}
  assume E = [n:int;l1:addr] @{pf_compa=array_v (int, l1, n), pf_compf=mfree_gc_v (l1), n=size_t n, pcomp=ptr l1, ncomp=int}

  val (pf_node_scc, pf_node_scc_free | p_node_scc) = array_ptr_alloc<int> ((i2sz)5)
  prval [l1:addr] EQADDR () = eqaddr_make_ptr (p_node_scc)
  
  val () = array_initize_elt<int> (!p_node_scc, (i2sz)5, ~1)
  var scc_info = @{pf_compa=pf_node_scc, pf_compf=pf_node_scc_free, n=(i2sz)5, pcomp=p_node_scc, ncomp=0} : E
  
  implement
  fundigraph_scc$beg<E> (env) = println!("beg of component: ", env.ncomp)
  implement
  fundigraph_scc$node<E> (v, env) = let
    prval [n:int] EQINT() = eqint_make_guint (env.n)
    val () = println!("component assigned: ", v, " to: ", env.ncomp)
    val v = $UN.cast{sizeLt(n)} (v)
    val () = !(env.pcomp).[v] := env.ncomp
  in
  end // end of [...]
  implement
  fundigraph_scc$end<E> (env) = let
    val () = env.ncomp := succ(env.ncomp)
  in
  end // end of [...]
   
  val () = println!("testing SCC:")
  val () = fundigraph_scc<E> (dg1, scc_info)
  val () = println!("total components identified: ", scc_info.ncomp)
  val () = println!("assignment of nodes to components: ")
  val () = fprint_array<int> (stdout_ref, !(scc_info.pcomp), scc_info.n)
  
  val () = array_ptr_free {int} (scc_info.pf_compa, scc_info.pf_compf | scc_info.pcomp)
}

