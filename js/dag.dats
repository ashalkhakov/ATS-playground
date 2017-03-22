// see also: http://agda.github.io/agda-stdlib/Data.Graph.Acyclic.html#1
#include
"share/atspre_define.hats"
#include
"{$LIBATSCC2JS}/staloadall.hats"

(* ****** ****** *)

staload
"{$LIBATSCC2JS}/SATS/print.sats"

#define ATS_MAINATSFLAG 1
#define ATS_DYNLOADNAME "my_dynload"

(* ****** ****** *)

// how to re-state the below using addresses?
// e.g. a node N may only contain pointers to nodes
// which are "less" than N

datatype GraphNode (node:t@ype, edge:t@ype, int) =
  | Empty (node, edge, 0) of ()
  | {n:nat} Node (node, edge, n + 1) of (Context (node, edge, n), GraphNode (node, edge, n))

where Context (node:t@ype, edge:t@ype, n:int) = '{
  label= node
, successors= List @(edge, natLt n)
}

typedef Graph (node:t@ype, edge:t@ype, n:int) = '{
  count= int n
, node= GraphNode (node, edge, n)
}
//
(* ****** ****** *)
//
fun context {n:nat} {m:int}
(node: int, l: list (@(int, natLt n), m)): Context (int, int, n) =
  '{label=node, successors= l}
//
fun node {n:nat}
  (n: int n, c: Context (int, int, n), g: GraphNode (int, int, n)): GraphNode (int, int, n+1) =
  Node (c, g)
//
(* ****** ****** *)
//
extern
fun
example(): void = "mac#"
implement
example() = let
  val n0 =
    node (4, context {4} (0, list_nil ()),
    node (3, context {3} (1, list_cons (@(10, 1), list_cons (@(11, 1), list_nil ()))),
    node (2, context {2} (2, list_cons (@(12, 0), list_nil ())),
    node (1, context {1} (3, list_nil ()),
    node (0, context {0} (4, list_nil ()), Empty))))) : GraphNode (int, int, 5)
  // what else can we do with such a DAG?
in
  print("Hello, world!")
end
//
(* ****** ****** *)
//
fun{N:t@ype}{E:t@ype}
index {n:pos;i:nat | i < n} (
  g: GraphNode (N, E, n)
, i: int i
): GraphNode (N, E, 1 + (n - (1 + i))) =
  if i = 0 then g
  else let
    val+Node (c, g) = g
    val i = i - 1
  in
    index (g, i)
  end
// end of [index]
//
(* ****** ****** *)
//
extern
fun
hello(): void = "mac#"
implement
hello() = print("Hello, world!")
//
(* ****** ****** *)
//
val () = hello()
//
(* ****** ****** *)

%{$
//
ats2jspre_the_print_store_clear();
my_dynload();
alert(ats2jspre_the_print_store_join());
//
%} // end of [%{$]
