staload _ = "prelude/DATS/list_vt.dats" (* template function definitions *)

(* ****** ****** *)

absviewtype repr (t@ype+, t@ype+) // kept abstract
extern
fun{a:t@ype} exp_cst (x: int): repr (a, int)
extern
fun{a:t@ype} exp_var (x: string): repr (a, int)
extern
fun{a:t@ype} exp_add (e1: repr (a, int), e2: repr (a, int)): repr (a, int)
// TODO: here, use a more detailed funenv type...
// (v:view, vt:viewtype) = (!v | _, !vt) -<fun> _
extern
fun{a:t@ype} exp_let (x: repr (a, int), f: (() -<cloptr> repr (a, int)) -<cloptr1> repr (a, int)): repr (a, int)
extern
fun{a:t@ype} exp_free (x: repr (a, int)): void

// use of this interface
// note that the functions being relied on
// haven't been defined yet!
fun{a:t@ype} test01 (): repr (a, int) =
  exp_add (exp_cst 10, exp_add (exp_var "x", exp_cst 20))

fun{a:t@ype} exp_a (): repr (a, int) = exp_add (exp_cst 10, exp_var "i1")
fun{a:t@ype} exp_b (): repr (a, int) =
  exp_add (exp_a (), exp_var "i2")

fun{a:t@ype} mul (n: int, x: repr (a, int)): repr (a, int) =
  if n = 0 then (exp_free x; exp_cst 0)
  else if n = 1 then x
  else begin
    if (n mod 2) = 0 then exp_let<a> (x,
      lam x' =<cloptr1> let
        val res = mul (n / 2, exp_add (x' (), x' ()))
      in cloptr_free x'; res end)
    else exp_let<a> (x,
      lam x' =<cloptr1> let
        val res = exp_add (x' (), mul (n-1, x' ()))
      in cloptr_free x'; res end)
  end // end of [begin]
// end of [mul]

fun{a:t@ype} exp_mul4 (): repr (a, int) = mul (4, exp_var "i1")

(* ****** ****** *)
(* we are now implementing the interface given above;
 * this is an abstract syntax tree with hash-consing
 *)

(* ****** ****** *)
(* establish a bidirectional mapping between
 * elements of a viewtype and pointers
 *)
absviewtype bimap (a:viewt@ype+)

// lookup a value in the bimap, and insert it if it's not there yet;
// otherwise, get rid of the term, and return its key
extern fun{a:viewt@ype} bimap_lookup_insert (x: a, bm: &bimap a, f: a -<> void) :<> ptr
extern fun{a:viewt@ype} bimap_empty () :<> bimap a
// just for testing purposes
extern fun{a:viewt@ype} bimap_appfun (bm: bimap a, f: (ptr, &a >> a?) -> void) : void

local

staload _ = "prelude/DATS/pointer.dats"
staload S = "libats/SATS/linmap_avltree.sats"
staload _ = "libats/DATS/linmap_avltree.dats"

viewtypedef vtype (a:viewt@ype) = [l:addr] (free_gc_v (a?, l), a @ l | ptr l)
assume bimap (a:viewt@ype) = $S.map (ptr, vtype a)

in // of [local]

implement $S.compare_key_key<ptr> (x1, x2, cmp) =
  if x1 < x2 then ~1 else if x1 > x2 then 1 else 0
// end of [compare_key_key]

implement{a}
bimap_empty () = $S.linmap_make_nil {ptr,vtype a} ()

implement{a}
bimap_lookup_insert (x0, bm, f) = let
  fn cmp (x1: ptr, x2: ptr):<cloref> Sgn = compare (x1, x2)
  // we need a stable identity for a viewtype element which
  // might have been allocated on stack, therefore a copy
  // on heap is necessary
  val [l:addr] (pf_gc, pf_at | p_at) = ptr_alloc<a> ()
  val () = ptr_set_vt<a> (pf_at | p_at, x0)
  val res = $S.linmap_search_ref (bm, p_at, cmp)
in
  if res > null then begin
    f (!p_at);
    ptr_free (pf_gc, pf_at | p_at);
    res
  end else let (* res = null *)
    var res1: vtype a? // uninitialized
    val b(*inserted*) = $S.linmap_insert<ptr,vtype a> (bm, p_at, (pf_gc, pf_at | p_at), cmp, res1)
    // this should never happen: we have already established
    // that the element is not in the map
    prval () = __discard (res1) where {
      extern prfun __discard {b:bool} (x: opt (vtype a, b)): void
    }
  in
    p_at
  end // end of [let]
end // end of [lookup_insert]

implement{a}
bimap_appfun (bm, f) = let
  var fp = f
  stavar l: addr
  val p = &fp: ptr l
  prval pf = view@ (fp)
  viewdef V = ((ptr, &a >> a?) -> void) @ l
  val () =
    $S.linmap_clear_funenv<ptr,vtype a> {V} {ptr l} (pf | bm, clo, p) where {
    fn clo (pf: !V | k: ptr, i: &vtype a >> vtype a?, env: !ptr l):<> void = let
      val (pf_gc, pf_at | p_at) = i
    in
      $effmask_all (!env (k, !p_at));
      ptr_free {a?} (pf_gc, pf_at | p_at)
    end // end of [clo]
  } // end of [where]
  prval () = view@ fp := pf
in
  $S.linmap_free<ptr,vtype a?> (bm)
end // end of [appfun]

end // of [local]

(* ****** ****** *)
(* the concrete representation of syntax *)

typedef nodeid = ptr
dataviewtype node = Ncst of int
  | Nvar of string
  | Nadd of (nodeid, nodeid)

extern
fun free_node (x: node) :<> void
implement
free_node (x) =
  case+ x of
  | ~Ncst _ => ()
  | ~Nvar _ => ()
  | ~Nadd _ => ()
// end of [free_node]

// a boxed linear type of closures
dataviewtype clo_vt (a:viewt@ype+, b:type+) =
  // this closure holds resources of type [env], and is equipped with a cleanup function
  {env:viewtype} CLOfn (a, b) of ((env, &a) -> b, env, env -> void)

dataviewtype pair_vt (a:viewt@ype+, b:viewt@ype+) = Ppair (a, b) of (a, b)
viewtypedef pair_vt (a:viewt@ype) = pair_vt (a, a)

assume repr (a:t@ype, b:t@ype) = clo_vt (bimap node, nodeid)

extern
fun hashcons (n: node): clo_vt (bimap node, nodeid)

implement
hashcons (n) = let
  fun f (e: node, bm: &bimap node): nodeid = bimap_lookup_insert (e, bm, free_node)
in
  CLOfn (f, n, free_node)
end

implement{a} exp_cst (x) = hashcons (Ncst x)
implement{a} exp_var (s) = hashcons (Nvar s)
implement{a} exp_add (e1, e2) = let
  viewtypedef env = pair_vt (repr (a, int))
  fun f (e: env, bm: &bimap node): nodeid = let
    val ~Ppair (~CLOfn (fe1, ee1, _), ~CLOfn (fe2, ee2, _)) = e
    val n1 = fe1 (ee1, bm)
    val n2 = fe2 (ee2, bm)
    val ~CLOfn (fpe, epe, _) = hashcons (Nadd (n1, n2))
  in
    fpe (epe, bm)
  end // end of [f]
  fun g (e: env): void = let
    val ~Ppair (~CLOfn (_, e1, g1), ~CLOfn (_, e2, g2)) = e
  in
    g1 (e1); g2 (e2)
  end // end of [g]
in
  CLOfn (f, Ppair (e1, e2), g)
end // end of [exp_add]

implement{a} exp_let (x, xf) = let
  viewtypedef env = pair_vt (repr (a, int), (() -<cloptr> repr (a, int)) -<cloptr1> repr (a, int))
  fun f (e: env, bm: &bimap node): nodeid = let
    val ~Ppair (~CLOfn (fe, ee, _), xf) = e
    val n1 = fe (ee, bm)
    fn fn1 () :<cloptr> repr (a, int) = CLOfn (eval, n1, free) where {
      fun eval (e: nodeid, bm: &bimap node): nodeid = e
      fun free (e: nodeid): void = ()
    } // end of [fn1]
    val ~CLOfn (fe1, e1, _) = xf fn1
  in
    cloptr_free xf;
    fe1 (e1, bm)
  end // end of [f]
  fun g (e: env): void = let
    val ~Ppair (~CLOfn (_, ee, ge), xf) = e
  in
    ge ee; cloptr_free xf
  end // end of [g]
in
  CLOfn (f, Ppair (x, xf), g)
end // end of [exp_let]

implement{a}
exp_free (x) = let
  val ~CLOfn (f, e, g) = x in g e
end // end of [exp_free]

fun{a:t@ype}
exp_run (e: repr (a, int)): void = let
  var m = bimap_empty ()
  val ~CLOfn (f, env, _) = e
  val h = f (env, m)
  val () = printf ("head is at %p\n", @(h))
  val () = bimap_appfun (m, lam (k,i) => begin
    print "(";
    case+ i of
    | Ncst x => (printf ("ncst(%d)", @(x)); fold@ i)
    | Nvar x => (printf ("nvar(%s)", @(x)); fold@ i)
    | Nadd (n1, n2) => (printf ("nadd(%p, %p)", @(n1, n2)); fold@ i);
    printf (") @ %p\n", @(k));
    free_node (i)
  end)
in
  // empty
end

(* ****** ****** *)

implement main (argc, argv) = let
  val exp01 = mul (6, exp_var "i1")
in
  exp_run (exp01)
end
