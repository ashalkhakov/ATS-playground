#include "share/atspre_staload.hats"
staload "./rows.dats"

(* ****** ****** *)

// new sort, with decidable equality
datasort
name = (*abstract*)

// what about rows?
// new sort, with decidable equality (maps names to t@ype's)
datasort
row = (*abstract*)
// need similar stuff also for prop's, view's, viewt@ype's

// decides if two rows are equal
stacst row_equal : (row, row) -> bool
stadef == = row_equal

(*
// is this necessary?
stacst row_subseteq : (row, row) -> bool
stadef <= = row_subseteq
*)

// similar to Ur/Web's ~ operator
stacst row_disjoint : (row, row) -> bool
symintr ~~
infixl ~~
stadef ~~ = row_disjoint // overloading

// new axioms of row's
stacst row_nil : row
stacst row_sing : (name,t@ype) -> row
// this needs a sublety: the name must not already
// exist in a row!
extern
praxi row_cons {n:name;t:t@ype;r:row | row_sing (n,t) ~~ r} (): [r1:row | r1 == ] void
stacst row_cons : (name, type) -> row -> row
symintr ::
infixr ::
stadef :: = row_cons

// e.g. (X, int) :: row_nil represents row type {X : int}

stacst row_merge : (row, row) -> row // this needs a sublety: the names must not overlap!
// i.e., row_merge (r1, r2) is legal if row_disjoint (r1, r2) == true
symintr ++
infixl ++
stadef ++ = row_merge

// similar to Ur/Web's $ operator (maps a row into the corresponding type)
// new type constructors:
// stacst make_rowtype : row -> type
// this is a new type constructor indexed by a row
// (needs some compiler support! the compiler must *know*
// what a given row maps to; not sure if patsolve can help with this)
// stacst make_record : row -> t@ype
// NOTE: make_rowtype can be derived:
// if rt = make_record (r), then make_rowtype (r) = '(rt)
// or something like that

abst@ype record (row)

// this is similar to a row, but it is more
// like a set of labels
// (that is, types that labels map to are completely ignored at runtime)
// TODO: rename? e.g. header
abst@ype rowheader (row)

// new type (for representing labels at runtime)
abstype label (name)

extern
fun label_make {n:name} (id: string): label (n)
// usage:
//   stacst Foo : name
//   val l1 = label_make {Foo} ("Foo")

extern
fun eq_label {n1,n2:name} (x: label (n1), y: label (n2)): bool (n1 == n2)
overload = with eq_label

extern
fun rowheader_nil () : rowheader (row_nil)

extern
fun{t:t@ype}
rowheader_extend
{n:name;r:row} | row_sing (n, t) ~~ r} (
  lab: label (n)
, rh: &rowheader (r)
): [rt1:t@ype] rowheader ((n,t) :: r)
// fun eq_label_label {n1,n2:name} (label (n1), label (n2)): bool (n1 == n2)

// record subscription (r.lab)
extern
fun{t:t@ype}
row_extract
  // if [r] contains it's own heading,
  // then it becomes simple to search for the matching label
  {r:row; n:name | row_sing (n, t) ~~ r}
  (r: &record ((n, t) :: r), lab: label (n), x: &_? >> t): void

// record update (r.lab := v)
extern
fun{t:t@ype}
row_update
  {r:row; n:name | row_sing (n, t) ~~ r}
  (r: &record ((n,t) :: r), lab: label (n), v: &t): void

extern
fun
row_merge
  {r1,r2:row | r1 ~~ r2}
  (r1: &record (r1), r2: &record (r2)): record (r1 ++ r2)

// rename one field of a row
extern
fun
row_rename1
  {r:row;t:t@ype;n1,n2:name | row_sing (n1, t) ~~ r; row_sing (n2, t) ~~ r} (
  r: &record ((n1, t) :: r)
, lab1: label (n1)
, lab2: label (n2)
): record ((n2, t) :: r)

// renamings (subst)? checking if rows are disjoint?
// - a subst is a mapping from names to names
// - subst needs to be a first-class object (record mapping to labels)
// what about many renamings? e.g. D4's rename operator?
// in D4, one may just map labels to other labels, and the renaming
// operator does all the necessary renamings in one go (much more higher-level)
// -- so renaming must be a first-class value too, similar to labels

// support for many renamings at once
abstype subst (row, row)

extern
fun sub_id {r:row} (): subst (r, r)

extern
fun
sub_name
{n1,n2:name;t:t@ype;r1,r2:row |
row_sing (n1, t) ~~ r1;
row_sing (n2, t) ~~ r2}
(
  l1: label (n1)
, l2: label (n2)
, sub: subst (r1, r2)
) : subst ((n1, t) :: r1, (n2, t) :: r2)

// apply the substitution
extern
fun
row_rename {r1,r2:row} (
  sub: subst (r1, r2)
, r: &record (r1)
) : record (r2)

// ex. r = {a=int,b=float}, fr = {x=string,y=double,a=int,b=float}
// sub = sub_id {r} () : subst (r, r)
// sub = sub_name (make_label<x>, make_label<z>, sub) : subst ((x,string) :: r, (z,string) :: r)
// sub = sub_name (make_label<y>, make_label<w>, sub) : subst ((y,double) :: (x,string) :: r, (w,double) :: (z,string) :: r)
// this is how fr is renamed into {w=double,z=string,a=int,b=float}

// the empty row
extern
fun row_nil () : record (row_nil)

// similar to row_merge, but for one field only
extern
fun{t:t@ype}
row_extend
{r:row;n:name | row_sing (n, t) ~~ r} (
  r: &record (r)
, lab: label n
, v: &t
): record ((n, t) :: r)

// drop labels given by [r2]
extern
fun{t:t@ype}
row_except
{r1,r2:row | r1 ~~ r2} (
  r: &record (r1 ++ r2))
, labs: &rowheader (r2)
): record (r1)

// more functions on rows?
// - something like Dataphor's redefine?
// - anything else to take from Dataphor?
// - join is interesting: Dataphor will check if two rows can be joined,
//   and if they can be, it will emit the code necessary to do so
//   - but we can't do the same! we must tell the user to specify
//     the fields to be joined on
extern
fun
join {r1,r2,r3:row | r1 ~~ r2 ~~ r2} (
  r1: &record (r1 ++ r2),
  r2: &record (r2 ++ r3),
  labs: &rowheader (r2)
): record (r1 ++ r3)

// over: given a row and a subset of field values,
// only select those field labels that the user wants
extern
fun{rt1,rt2:t@ype}
row_over
{r1,r2:row | r1 ~~ r2} (
  r: &record (r1 ++ r2)
, cols: &rowheader (r1)
): record (r1)

// subtyping:
//
// given rows R1, R2 such that R1 is a subrow of R2,
// we will want to be able to apply functions taking R1 as input
// also to R2
//
// shall we define row casting operations? R2 to R1 (just a projection)
// - no, row_over already does that

// we should also support more operations on rowheader
// - row_merge
// - row_rename1
// - row_rename
// - row_nil
// - row_extend
// - row_except
// - row_over
//
// additionally, it would be quite useful to be able to test
// if a given label actually is contained in a rowheader
// at run-time

// similarly, more operations are needed on subst, because
// it's also a set, just with a different codomain
// - composition of substitutions
//   - apply subst after another subst
// - subrows
//   - if s is for row R, and R is a subrow of T,
//     then s must also apply to T

// folds?
// better not! that's too much of a hassle

(* ****** ****** *)

// let's think how we should implement this.
//
// - a rowheader is just a map from labels to offsets (see my other note)
//   - if needed, we can even supply tags for a limited run-time type information
// - a row is just an extensible tuple (see my other note),
//   BUT it conforms to a rowheader (which means: we know the exact order of the fields)
//   - a record is tied to a rowheader by a common t@ype index
//   - we must not rely on the order of the fields in a record (it can be arbitrary)
//   - the "order" part is what requires a "folder" (in Ur/Web's parlance)
//   - the sort row is for unordered records, so {X:int,Y:float} = {Y:float,X:int}
//   - at run-time, we shall use one canonical ordering (lexicographic order on labels)
//   - what about the row header? shall it not be used as a folder too?
//   - at run-time, folders are used to override the canonical ordering (a folder is indexed by the same row variable as the row it is for)

// canonical ordering on labels
stacst name_lte : (name, name) -> bool
stadef <= = name_lte

extern
fun lte_label {n1,n2:name} (x: label (n1), y: label (n2)): bool (name_lte (n1, n2))

// stacst name_row_lt : (name, row) -> bool
// stadef < = name_row_lt

// idea: row_layout (r, ts, t)
// means that r is represented as a sequence of types ts, which maps to type t
// (we could always, I think, defer that to run-time actually)
abstype row_layout (row, t0ypes, t@ype, int)
// let's skip row_layout constructors for now
// it suffices to say that row_layout will prescribe
// some linearized, canonical memory layout to row elements

extern
fun row_layout_nil () : row_layout (row_nil, t0ypes_nil, void, 0)

extern
fun
row_layout_insert
  {n:name;a,b:t@ype;r:row;ts:t0ypes;nl:int | row_sing (n, a) ++ r} (
  // [n] must be less than any other label in the row
  // for it to be *prepended* to the list
  // (in general I think it's hard to guarantee the precise type)
  lab: label n
, ty: t0ype_t a
, rl: row_layout (r, ts, b, nl)
) : [ts1:t0ypes;c:t@ype] row_layout (row_sing (n, a) ++ r, ts1, c, nl+1)

// when destructuring the row layout, we may still learn the precise type!
// two cases to handle:
// - nil row (row_layout is actually empty!)
// - label and t0ype_t prepended to another row layout

extern
fun
row_layout_isempty {r:row;ts:t0ypes;t:t@ype;nl:int} (
  rl: row_layout (r, ts, t, nl)
): bool (nl == 0 && r == row_nil && ts == t0ypes_nil)

// this is an attempt at pattern-matching
extern
fun
row_layout_nonempty {r:row;ts:t0ypes;t:t@ype;nl:pos} (
  rl: &row_layout (r, ts, t, nl) >> row_layout (r', ts', b, nl-1)
, lab: &_? >> label n
, ty: &_? >> t0ype_t a
) : #[a,b:t@ype;r':row;ts':t0ypes | r' == (n,a)::r; ts == t0ypes_cons (a, ts')] (
  TypeEq (t, @(a,b)) | void
)

(*
now, what is a row? it's a pair: rowlayout + a pointer to an unknown flat type
- I think that row layouts need to be cached somehow, we want to share them as much
  as possible
- we could also make the users choose where they want rowlayout stored
  - yeah, they could also thread it as much as they want
  - for instance, we only need one row layout for many rows in a result set
- type-passing stuff: row layout is information about the type of the row at runtime

once we have the row layout at runtime, it becomes possible to represent rows
as simple tuples, and then index into them in O(log n) (we'll keep a map from labels
to offsets), and in O(1) if you have an offset

*)

// this can be done once, used many times
extern
fun{a,t:t@ype}
row_resolve
  {n:name;r:row;ts:t0ypes | row_sing (n,a) ~~ r} (
  rl: row_layout (row_sing (n,a) ++ r, ts, t)
, r: &t
, lab: label (n)
) : Offset_t (a, t)

(*
given row_layout (r, ts, t):
- we always know the flat type of tuple t, that represents r
- we also know the order of elements in tuple t (that's ts)
- and finally, records are now simple types t

two records indexed by the same row are guaranteed to have compatible
row layouts (and the same type)

one thing worth noting is that users will request some ordering when rows
are being output to the screen... what can we do about that? does every
row need to carry some ordering too?
*)

// the above seems like something entirely doable; but to make things
// usable, we will have to discharge lots of proofs of record disjointness
// somehow
// - we could discharge the proofs at run-time (by actually testing rowheaders
//   for disjointness)
//   - only as a last resort please!
// - we should extend ATS2 statics
//   - wdblair's patsolve project (ATS-Postiats-contrib/projects/MEDIUM/ATS-extsolve)
//   - ATS-Postiats-contrib/contrib/libats-/wdblair/patsolve (some examples)
//   - usage of the above: https://github.com/githwxi/ATS-Postiats-contrib/tree/master/contrib/libats-/wdblair/prelude
//   - where are the decision procedures implemented?
//     - in contrib/libats-/wdblair/prelude/SMT
