// a finally tagless hash-consing evaluator

(* ****** ****** *)

absviewt@ype repr (t@ype+, t@ype+) // kept abstract
extern
fun{a:t@ype} exp_cst (x: int): repr (a, int)
extern
fun{a:t@ype} exp_var (x: string): repr (a, int)
extern
fun{a:t@ype} exp_add (e1: repr (a, int), e2: repr (a, int)): repr (a, int)
// TODO: here, use a more detailed funenv type...
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
 * this is an abstract syntax tree representation
 * with hash-consing
 *)

(* ****** ****** *)
(* establish a bidirectional mapping between
 * elements of a (boxed) viewtype and pointers
 *)
absviewtype bimap (a:viewtype+)

typedef hash_fun (a:viewtype) = (!a) -<> ulint
typedef eq_fun (a:viewtype) = (!a, !a) -<> bool

// lookup a value in the bimap, and insert it if it's not there yet;
// otherwise, get rid of the term, and return its key
extern fun bimap_lookup_insert {a:viewtype} (x: a, bm: &bimap a, f: a -<> void) :<> ptr
extern fun bimap_empty {a:viewtype} (hash: hash_fun a, eq: eq_fun a) :<> bimap a
// just for testing purposes
extern fun bimap_appfun {a:viewtype} (bm: bimap a, f: (ptr, a) -> void) : void

local

staload _ = "prelude/DATS/pointer.dats"
staload _ = "prelude/DATS/list_vt.dats" // template functions used in hashtable_chain
staload H = "libats/SATS/hashtable_chain.sats"
staload _ = "libats/DATS/hashtable_chain.dats"

viewtypedef vtype (a:viewt@ype) = [l:addr] (free_gc_v (a?, l), a @ l | ptr l)

assume bimap (a:viewt@ype) = [l:agz] $H.HASHTBLptr (ptr, vtype a, l)

typedef key = ptr

in // of [local]

implement
bimap_empty {a} (hfn, eqfn) = let
  // since keys are always valid pointers, this is safe
  extern
  castfn __cast (x: key)
    :<> [l:addr] (a @ l, a @ l -<lin,prf> void | ptr l)

  fn hash (x: key):<cloref> ulint = let
    val (pf_at, fpf | p_at) = __cast (x)
    val res = hfn (!p_at)
    prval () = fpf (pf_at)
  in
    res
  end // end of [hash]
  // end of [hash]
  fn eq (x1: key, x2: key):<cloref> bool = let
    // since keys are always valid pointers, this is safe
    val (pf_at1, fpf1 | p_at1) = __cast (x1)
    val (pf_at2, fpf2 | p_at2) = __cast (x2)
    val res = eqfn (!p_at1, !p_at2)
    prval () = fpf1 (pf_at1) and () = fpf2 (pf_at2)
  in
    res
  end // end of [eq]
in
  $effmask_all ($H.hashtbl_make {ptr,vtype a} (hash, eq))
end // end of [bimap_empty]

implement
bimap_lookup_insert {a} (x0, bm, f) = let
  // we need a stable identity for a viewtype element which
  // might have been allocated on stack, therefore a copy
  // on heap is necessary
  val [l:addr] (pf_gc, pf_at | p_at) = ptr_alloc<a> ()
  val () = !p_at := x0
  // we won't deallocate any items until the very end,
  // so this is safe
  val res = $H.hashtbl_search_ref (bm, p_at)
in
  if res > null then begin
    f (!p_at);
    ptr_free (pf_gc, pf_at | p_at);
    res
  end else begin (* res = null *)
    $H.hashtbl_insert<ptr,vtype a> (bm, p_at, (pf_gc, pf_at | p_at));
    p_at
  end // end of [let]
end // end of [lookup_insert]

implement
bimap_appfun {a} (bm, f) = let
  fun loop {n:nat} .<n>. (
    xs: list_vt (@(key, vtype a), n)
  ) :<cloref> void =
    case+ xs of
    | ~list_vt_nil () => ()
    | ~list_vt_cons (@(k, i), xs') => let
        val (pf_gc, pf_at | p_at) = i
        val () = $effmask_all (f (k, !p_at))
        val () = ptr_free (pf_gc, pf_at | p_at)
      in
        loop (xs')
      end // end of [let]
  // end of [loop]
  val lst = $H.hashtbl_listize_free<key,vtype a> (bm)
  val () = loop (lst)
in
  // empty
end // end of [appfun]

end // of [local]

(* ****** ****** *)
(* the concrete representation of syntax *)

typedef nodeid = ptr
dataviewtype node = Ncst of int
  | Nvar of string
  | Nadd of (nodeid, nodeid)

extern fun node_eq : eq_fun (node)
implement node_eq (x, y) = case+ (x, y) of
  | (Ncst a, Ncst b) => let val res = (a = b) in fold@ x; fold@ y; res end
  | (Nvar a, Nvar b) => let val res = (a = b) in fold@ x; fold@ y; res end
  | (Nadd (a, b), Nadd (c, d)) => let val res = (a = c) && (b = d) in fold@ x; fold@ y; res end
  | (_, _) => false
// end of [node_eq]

%{$
// this code is adapted from Boost.Functional.Hash
ats_ulint_type
hash_int (ats_int_type x) {
  // not very fast, but portable
  const size_t bits = sizeof(ats_ulint_type)*8 ;
  const size_t length = (sizeof(ats_int_type)*8-1) * bits ;
  ats_ulint_type seed = 0 ;
  ats_int_type positive = x < 0 ? -1 - x : x ;
  ats_size_type i = length * bits ;

  while (i > 0) {
    seed ^= (ats_ulint_type)(positive >> i) + (seed<<6) + (seed>>2) ;
    i -= bits ;
  }
  seed ^= (ats_ulint_type)x + (seed<<6) + (seed>>2) ;
  return seed ;
} // end of [hash_int]
ats_ulint_type
hash_ptr (ats_ptr_type x) {
  // not very fast, but portable
  const size_t bits = sizeof(ats_ulint_type)*8 ;
  const size_t length = (sizeof(ats_ptr_type)*8-1) * bits ;
  ats_ulint_type seed = 0 ;
  ats_size_type i = length * bits ;

  while (i > 0) {
    seed ^= (((ats_ulint_type)x) >> i) + (seed<<6) + (seed>>2) ;
    i -= bits ;
  }
  seed ^= (ats_ulint_type)x + (seed<<6) + (seed>>2) ;
  return seed ;
} // end of [hash_ptr]
%}

extern fun node_hash : hash_fun (node)
implement node_hash (x) = let
  fn hash_string (x: string) :<> ulint = string_hash_33 x
  extern fun hash_int (x: int) :<> ulint = "hash_int"
  extern fun hash_ptr (x: ptr) :<> ulint = "hash_ptr"
  fn hash_combine (seed: ulint, x: ulint) :<> ulint =
    (seed lxor x + (ulint_of_uint 0x9e3779b9u) + (seed << 6) + (seed >> 2))
  // end of [hash_combine]
in
  case+ x of
  | Ncst a => let val res = hash_int a in fold@ x; res end
  | Nvar a => let val res = hash_string a in fold@ x; res end
  | Nadd (a, b) => let
      // this is admissible because physical equality
      // is equivalent to structural equality
      val res = hash_combine (hash_ptr a, hash_ptr b)
    in
      fold@ x; res
    end // end of [let]
end // end of [node_hash]

extern
fun free_node (x: node) :<> void
implement
free_node (x) =
  case+ x of
  | ~Ncst _ => ()
  | ~Nvar _ => ()
  | ~Nadd _ => ()
// end of [free_node]

viewtypedef clo_vt (a:viewt@ype, b:type) =
  [env:viewtype] ((env, &a) -> b, env, env -> void)
// end of [clo_vt]

dataviewtype pair_vt (a:viewt@ype+, b:viewt@ype+) = Ppair (a, b) of (a, b)
viewtypedef pair_vt (a:viewt@ype) = pair_vt (a, a)

assume repr (a:t@ype, b:t@ype) = clo_vt (bimap node, nodeid)

extern
fun hashcons (n: node): clo_vt (bimap node, nodeid)

implement
hashcons (n) = let
  fun f (e: node, bm: &bimap node): nodeid = bimap_lookup_insert (e, bm, free_node)
in
  (f, n, free_node)
end

implement{a} exp_cst (x) = hashcons (Ncst x)
implement{a} exp_var (s) = hashcons (Nvar s)
implement{a} exp_add (e1, e2) = let
  viewtypedef env = pair_vt (repr (a, int))
  fun f (e: env, bm: &bimap node): nodeid = let
    val ~Ppair (fst, snd) = e
    val n1 = fst.0 (fst.1, bm)
    val n2 = snd.0 (snd.1, bm)
    var pe = hashcons (Nadd (n1, n2))
  in
    pe.0 (pe.1, bm)
  end // end of [f]
  fun g (e: env): void = let
    val ~Ppair ((_, e1, g1), (_, e2, g2)) = e
  in
    g1 (e1); g2 (e2)
  end // end of [g]
in
  (f, Ppair (e1, e2), g)
end // end of [exp_add]

implement{a} exp_let (x, xf) = let
  viewtypedef env = pair_vt (repr (a, int), (() -<cloptr> repr (a, int)) -<cloptr1> repr (a, int))
  fun f (e: env, bm: &bimap node): nodeid = let
    val ~Ppair ((fe, ee, _), xf) = e
    val n1 = fe (ee, bm)
    fn fn1 () :<cloptr> repr (a, int) = (eval, n1, free) where {
      fun eval (e: nodeid, bm: &bimap node): nodeid = e
      fun free (e: nodeid): void = ()
    } // end of [fn1]
    val (fe1, e1, _) = xf fn1
  in
    cloptr_free xf;
    fe1 (e1, bm)
  end // end of [f]
  fun g (e: env): void = let
    val ~Ppair ((_, ee, ge), xf) = e
  in
    ge ee; cloptr_free xf
  end // end of [g]
in
  (f, Ppair (x, xf), g)
end // end of [exp_let]

implement{a}
exp_free (x) = let
  val (f, e, g) = x in g e
end // end of [exp_free]

fun{a:t@ype}
exp_run (e: repr (a, int)): void = let
  var m = bimap_empty (node_hash, node_eq)
  val (f, env, _) = e
  val h = f (env, m)
  val () = printf ("head is at %p\n", @(h))
  // sadly, hash map is unordered...
  val () = bimap_appfun (m, lam (k, i) => begin
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
  // this expression presents both an opportunity
  // for explicit sa well as implicit sharing
  val exp01 = exp_add (mul (6, exp_var "i1"), exp_var "i1")
in
  exp_run (exp01)
end
