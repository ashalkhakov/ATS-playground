
#include
"share/atspre_staload.hats"

// based on: http://cs.brynmawr.edu/~rae/papers/2012/singletons/paper.pdf
// new operators:
// X group by L
// where L is a list of grouping attributes of X (list of column names by which
// to group), then
// list of A1 = aggregate-op(A), where A1 is fresh column in X,
// aggregate-op is an aggregate operation, and A is a column of X

(* ****** ****** *)

datasort U = BOOL | STRING | NAT | VEC of (U, int)

dataprop EL (U, t@ype) =
  | EL_BOOL (BOOL, bool)
  | EL_STRING (STRING, string)
  | EL_NAT (NAT, int)
extern
praxi El : {u:U} () -> [a:t@ype] EL (u, a)
extern
praxi EL_bool : EL (BOOL, bool)
extern
praxi EL_string : EL (STRING, string)
extern
praxi EL_nat : EL (NAT, int)

datatype IU (U) =
 | BOOL (BOOL)
 | STRING (STRING)
 | NAT (NAT)
 //| VEC of (U, int)

dataprop EQU (U, U) = {u:U} EQU (u, u) // refl

stacst eq_string_string : (string,string)->bool
abstype
literal_string(string) = $extype"atsliteral_string"
extern
fun
eq_string_string {s1,s2:string}
(literal_string(s1), literal_string(s2)): bool (eq_string_string (s1, s2)) = "mac#eq_string_string"

(* ****** ****** *)

datasort Attribute = Attr of (string, U)
datasort Schema = Schema_nil | Schema_cons of (Attribute, Schema)

dataprop EQSchema (Schema,Schema) = {s:Schema} EQSchema (s, s)

datatype ISchema (Schema) =
  | ISchema_nil (Schema_nil)
  | {name:string;u:U;s:Schema} ISchema_cons (Schema_cons (Attr(name,u), s)) of ((*string(name),*) IU (u), ISchema (s))

(* ****** ****** *)

%{^
typedef
union { atstype_int i; atstype_bool b; atstype_string s; } datavalue ;
//
#define datavalue_get_int(x) (((datavalue*)x)->i)
#define datavalue_get_bool(x) (((datavalue*)x)->b)
#define datavalue_get_string(x) (((datavalue*)x)->s)
#define datavalue_set_int(x, v) (((datavalue*)x)->i = v)
#define datavalue_set_bool(x, v) (((datavalue*)x)->b = v)
#define datavalue_set_string(x, v) (((datavalue*)x)->s = v)
%}

abst@ype
datavalue(tag:U) = $extype"datavalue"
//
typedef datavalue = [tag:U] datavalue (tag)
//
extern
fun datavalue_get_int (x: &datavalue(NAT)): int = "mac#"
extern
fun datavalue_get_bool (x: &datavalue(BOOL)): bool = "mac#"
extern
fun datavalue_get_string (x: &datavalue(STRING)): string = "mac#"
extern
fun datavalue_set_int
  (x: &datavalue? >> datavalue(NAT), i: int): void = "mac#"
extern
fun datavalue_set_bool
(x: &datavalue? >> datavalue(BOOL), b: bool): void = "mac#"
extern
fun datavalue_set_string
(x: &datavalue? >> datavalue(STRING), s: string): void = "mac#"
//
extern
fun{a:t@ype} datavalue_get_value {u:U}
(EL (u, a) | x: &datavalue(u)): a
extern
fun{a:t@ype} datavalue_set_value {u:U}
(EL (u, a) | x: &datavalue? >> datavalue(u), a): void
//
implement
datavalue_get_value<bool> (pf_el | x) = let
  prval EL_BOOL () = pf_el in
  datavalue_get_bool (x)
end
implement
datavalue_get_value<int> (pf_el | x) = let
  prval EL_NAT () = pf_el in
  datavalue_get_int (x)
end
implement
datavalue_get_value<string> (pf_el | x) = let
  prval EL_STRING () = pf_el in
  datavalue_get_string (x)
end
implement
datavalue_set_value<bool> (pf_el | x, v) = let
  prval EL_BOOL () = pf_el in
  datavalue_set_bool (x, v)
end
implement
datavalue_set_value<int> (pf_el | x, v) = let
  prval EL_NAT () = pf_el in
  datavalue_set_int (x, v)
end
implement
datavalue_set_value<string> (pf_el | x, v) = let
  prval EL_STRING () = pf_el in
  datavalue_set_string (x, v)
end
//
extern
fun int2datavalue (x: int): datavalue(NAT)
extern
fun bool2datavalue (x: bool): datavalue(BOOL)
extern
fun string2datavalue (x: string): datavalue(STRING)
//
implement
int2datavalue (v) = let
  var x: datavalue
  val () = datavalue_set_int (x, v) in
  x
end
implement
bool2datavalue (v) = let
  var x: datavalue
  val () = datavalue_set_bool (x, v) in
  x
end
implement
string2datavalue (v) = let
  var x: datavalue
  val () = datavalue_set_string (x, v) in
  x
end
//
extern
fun{a:t@ype}
geq_value_value (a, a): bool
implement
geq_value_value<bool> (x, y) = (x = y)
implement
geq_value_value<int> (x, y) = (x = y)
implement
geq_value_value<string> (x, y) = (x = y)
//
(* ****** ****** *)

// TODO: better row representation (just a flat array of datavalues)
datatype Row (Schema) =
  | EmptyRow (Schema_nil) of List(int)
  | {u:U}{s:Schema}{name:string} ConsRow (Schema_cons (Attr (name, u), s)) of (datavalue (u), Row s)

abstype Table (Schema) = ptr
//typedef Table (s:Schema) = List (Row(s)) // TODO: better table representation!
extern
fun
list2Table {s:Schema} (List (Row s)): Table (s)
extern
fun
Table_foreach {s:Schema} (Table(s), Row(s) -> void): void

abstype Handle (Schema) = ptr

// append two schemas
dataprop
Append (Schema, Schema, Schema) =
  | {s:Schema} Append_nil (Schema_nil, s, s)
  | {a:Attribute;s,t,r:Schema} Append_cons (Schema_cons (a, s), t, Schema_cons (a, r))
    of (Append (s, t, r))

// check that a schema is free of a certain attribute
dataprop
AttrNotIn (Attribute,Schema,bool) =
  | {a:Attribute} AttrNotIn_nil (a, Schema_nil, true)
  | {name,name':string;u,u':U;t:Schema;b1:bool} AttrNotIn_cons (Attr (name, u), Schema_cons (Attr (name', u'), t), ~eq_string_string(name, name') && b1)
      of AttrNotIn (Attr (name, u), t, b1)

// check that two schemas are disjoint
dataprop
Schema_disjoint (Schema,Schema, bool) =
  | Schema_disj_emp (Schema_nil, Schema_nil, true)
  | {h:Attribute}{t,s:Schema} {b1,b2:bool} Schema_disj_cons (Schema_cons (h, t), s, b1 && b2) of (AttrNotIn (h, s, b1), Schema_disjoint (t, s, b2))

extern
fun
row_join {s,s',r:Schema} (Schema_disjoint (s,s',true), Append (s, s', r) | Row (s), Row (s')): Row (r)
implement
row_join {s,s',r} (pf_disj, pf_app | rs, rs') = let
  // how to implement
  fun
  loop {s1,s2:Schema} (x1: Row (s1), x2: Row (s2)): [r:Schema] (Append (s1, s2, r) | Row r) =
    case+ x1 of
    | EmptyRow (_) => (Append_nil () | x2)
    | ConsRow (xv1, x1) => let
        val (pf_app | r) = loop (x1, x2)
      in
        (Append_cons (pf_app) | ConsRow (xv1, r))
      end
  val (pf1_app | r) = loop (rs, rs')
  prval EQSchema () = __trustme (pf1_app, pf_app) where {
      // append is functional
      extern prfun __trustme {s1,s2,r1,r2:Schema} (Append (s1, s2, r1), Append (s1, s2, r2)): EQSchema (r1,r2)
  }
in
  r
end // end of [row_join]

extern
fun{}
row_foreach$tmp {u:U} (datavalue(u)): void
extern
fun{}
row_foreach {s:Schema} (Row(s)): void
implement
row_foreach<> {s} (r) = let
  fun
  loop {s:Schema} (r: Row(s)): void =
    case+ r of
    | EmptyRow (_) => ()
    | ConsRow (x, r) => (row_foreach$tmp<> (x); loop (r))
in
  loop (r)
end

dataprop InProof (l:string, u:U, Schema, int) =
  | {s:Schema} InElt (l, u, Schema_cons (Attr (l, u), s), 0)
  | {a2:Attribute;s:Schema;n:nat} InTail (l, u, Schema_cons (a2, s), n+1) of InProof (l, u, s, n)

datatype SubsetProof (Schema, Schema) =
  | {s:Schema} SubsetEmpty (Schema_nil, s)
  | {attrs:Schema;name:string;u:U;s':Schema;n:int} SubsetCons (Schema_cons (Attr (name, u), attrs), s')
      of (InProof (name,u, s', n) | int n, SubsetProof (attrs, s'))

extern
fun
row_get {nm:string;u:U;sch:Schema;n:int} (
  InProof (nm, u, sch, n) | n: int n, r: Row sch
): datavalue(u)

implement
row_get {nm,u,sch,n} (pfin | n, r) = let
in
  if n = 0 then let
    prval InElt {lab,u1} () = pfin
    val+ ConsRow {u1} (x, r) = r
  in
    x
  end else let
    prval InTail pfin = pfin
    val n = n - 1
    val+ ConsRow (_, r) = r
  in
    row_get (pfin | n, r)
  end
end

extern
fun
row_project {s,s':Schema} (SubsetProof (s, s'), Row(s')): Row(s)
implement
row_project {s,s'} (sub, r) = let
  fun
  loop {s,s':Schema} (sub: SubsetProof (s, s'), r: Row (s')): Row (s) =
    case+ sub of
    | SubsetEmpty () => EmptyRow (list_nil ())
    | SubsetCons (pf_in | n, sub) => let
        val x = row_get (pf_in | n, r)
        val res = loop (sub, r)
    in
        ConsRow (x, res)
    end
in
  loop (sub, r)
end

datatype Expr (Schema, U) = // type for expressions
  // column reference
  | {name:string;u:U;n:int;s:Schema} Element (s, u) of (InProof (name,u,s,n) | int n)
  // literals
  | {u:U}{s:Schema} Lit (s, u) of datavalue(u)
  // scalar operations
  | {s:Schema} LessThan (s, BOOL) of (Expr (s, NAT), Expr (s, NAT))
  | {s:Schema} Equals (s, BOOL) of (Expr (s, NAT), Expr (s, NAT)) // FIXME: cannot make this polymorphic

// type for relational algebra expressions
datatype RA (Schema) =
  | {s:Schema} RAread (s) of Table (s) // TODO: Handle (s) instead of Table (s)!
  | {s:Schema} RAunion (s) of (RA (s), RA (s))
  | {s:Schema} RAdiff (s) of (RA (s), RA (s))
  // TODO: renaming
  // | {s,s':Schema} RArename (s') of (Subst (s, s') RA (s))
  | {s,s',r:Schema} RAjoin (r) // actually theta-join
     of (Schema_disjoint (s,s',true), Append (s, s', r) | RA (s), RA (s'), Expr (r, BOOL))
  | {s,s':Schema} RAproject (s') of (SubsetProof (s', s), RA s)
  | {s:Schema} RAselect (s) of (Expr (s, BOOL), RA s)

// performs type-checking that the given parameter conforms to the schema
extern
fun
connect {s:Schema} (string, ISchema s): Handle s
// performs a RA query evaluation
extern
fun
query {s:Schema} ((*TODO: ISchema s,*) RA s): List (Row s)

extern
fun{a:t@ype}
extractElt {nm:string;u:U;sch:Schema;n:int;l:addr} (
  pf_at : !(a? @ l) >> a @ l, pf_el : EL (u, a), pf: InProof (nm, u, sch, n)
| n: int n, r: Row sch, p_res: ptr l
): void

implement{A}
extractElt {nm,u,sch,n,l} (
  pfres, pfel, pfin(*, pfti*) | n, r, pres
) = let
in
  if n = 0 then let
    prval InElt {lab,u1} () = pfin
    val+ ConsRow {u1} (x, r) = r
    var x = x
    val x1 = datavalue_get_value<A> (pfel | x)
    val () = ptr_set<A>(pfres | pres, x1)
  in
  end else let
    prval InTail pfin = pfin
    val n = n - 1
    val+ ConsRow (_, r) = r
  in
    extractElt<A> (pfres, pfel, pfin | n, r, pres)
  end
end

extern
fun{a:t@ype}
eval_expr {u:U}{s:Schema}{l:addr} (pf_res: !(a? @ l) >> a @ l, EL (u, a) | Row s, Expr (s, u), ptr l): void
implement{a}
eval_expr {u}{s}{l} (pfres, pf_el | row, e, pres) = let
  // EL (u, a)
in
  case- :(pfres : a @ l) => e of
  | Element (pf_in | n) => let
      prval () = __assert (pf_in) where { extern prfun __assert {n:int}{nm:string;u:U;sch:Schema} (InProof (nm, u, sch, n)): [n>=0] void }
      val () = extractElt<a> (pfres, pf_el, pf_in | n, row, pres)
    in
    end
  | Lit (v) => let
      var v = v
      val v = datavalue_get_value<a> (pf_el | v)
    in
      ptr_set (pfres | pres, v)
    end
  | LessThan (o1, o2) => let
      prval EL_BOOL () = pf_el
      var x1: int
      var x2: int
      val () = eval_expr<int> (view@x1, EL_nat | row, o1, addr@ x1)
      val () = eval_expr<int> (view@x2, EL_nat | row, o2, addr@ x2)
    in
      ptr_set (pfres | pres, (x1 < x2))
    end
  | Equals (o1, o2) => let
      prval EL_BOOL () = pf_el
      var x1: int
      var x2: int
      val () = eval_expr<int> (view@x1, EL_nat | row, o1, addr@ x1)
      val () = eval_expr<int> (view@x2, EL_nat | row, o2, addr@ x2)
    in
      ptr_set (pfres | pres, geq_value_value<int> (x1, x2))
    end
end

local

assume Table (s:Schema) = List (Row s)

in // in-of-local

implement
list2Table {s} (xs) = xs

implement
Table_foreach {s} (xs, f) = loop (xs) where {
  fun
  loop {n:int} (xs: list (Row s, n)): void =
    case+ xs of
    | list_cons (x, xs) => (f (x); loop (xs))
    | list_nil () => ()
}

implement
query {s} ((*schm,*) ra) =
  case- ra of
  | RAread tab => tab // need a better representation for a table
  | RAunion (ra1, ra2) => let
      val r1 = query (ra1)
      val r2 = query (ra2)
      val res = list_append (r1, r2)
    in
      res
    end
    (*
  | RAdiff (ra1, ra2) => let
      // all tuples in ra1 but NOT in ra2
      // this is where we need something akin to C++ Boost.MultiIndex...
      // how to implement THAT, given our row representation?
      // - we can have a list of indexes, a tuple of indexes... every index comes with a subset proof
    in
    end
  *)
  | RAproject {s',s} (sub, ra) => let
        val r = query (ra)
        fun
        loop {n:int} (sub: SubsetProof (s, s'), xs: list (Row s', n), acc: List0 (Row s)): List0 (Row s) =
            case+ xs of
            | list_nil () => acc
            | list_cons (x, xs) => let
                val x = row_project (sub, x)
              in
                loop (sub, xs, list_cons (x, acc))
              end
        val res = loop (sub, r, list_nil ())
    in
      res
    end // end of [RAproject]
  | RAjoin {s,s',r} (pf_disj, pf_app | ra1, ra2, theta) => let
        val r1 = query (ra1)
        val r2 = query (ra2)
        fun
        loop1 {n:int} (xs: list (Row s, n), acc: List0 (Row r)): List0 (Row r) =
            case+ xs of
            | list_nil () => acc
            | list_cons (x, xs) => let
                val acc = loop2 (x, r2, acc)
              in
                loop1 (xs, acc)
              end
        and
        loop2 {n:int} (x: Row s, ys: list (Row s', n), acc: List0 (Row r)): List0 (Row r) =
            case+ ys of
            | list_nil () => acc
            | list_cons (y, ys) => let
                val row = row_join (pf_disj, pf_app | x, y)
                var b: bool
                val () = eval_expr<bool> (view@ b, EL_bool | row, theta, addr@ b)
              in
                loop2 (x, ys, if b then list_cons (row, acc) else acc)
              end
        // end of [loop2]
        val res = loop1 (r1, list_nil ())
    in
        res
    end // end of [RAjoin]
  | RAselect (e, ra) => let
      val res = query ((*schm,*) ra)
      fun
      pred(r: Row s): bool = let
        var x: bool
        val () = eval_expr<bool> (view@ x, EL_bool | r, e, addr@ x)
      in
        x
      end
      val res = loop (res, list_nil ()) where {
          fun
          loop (xs: List (Row s), acc: List (Row s)): List (Row s) =
            case+ xs of
            | list_nil () => acc
            | list_cons (x, xs) => let
              prval () = lemma_list_param(xs)
              prval () = lemma_list_param (acc)
            in
              if pred (x) then loop (xs, list_cons (x, acc))
              else loop (xs, acc)
            end
      }
    in
      res
    end

end // end of [local]

(* ****** ****** *)

// construct a table first
#define R ConsRow

stadef lab_firstname = "firstname"
stadef lab_lastname = "lastname"
stadef lab_deptid = "deptid"

stadef EmployeeFirstName_attr = Attr (lab_firstname, STRING)
stadef EmployeeLastName_attr = Attr (lab_lastname, STRING)
stadef EmployeeDeptID_attr = Attr (lab_deptid, NAT)

stadef EmployeeSchema =
Schema_cons (EmployeeLastName_attr,
Schema_cons (EmployeeFirstName_attr,
Schema_cons (EmployeeDeptID_attr,
Schema_nil ())))

val employeeTable =
list2Table (
  $list{Row EmployeeSchema}(
    R (string2datavalue ("Weirich"), R (string2datavalue("S"), R (int2datavalue(1),  EmptyRow ($list{int}(0))))),
    R (string2datavalue ("Eisenberg"), R (string2datavalue("R"), R (int2datavalue(2), EmptyRow ($list{int}(1)))))
  )
)


stadef lab_id = "id"
stadef DeptID_attr = Attr (lab_id, NAT)
stadef lab_deptname = "deptname"
stadef DeptName_attr = Attr (lab_deptname, STRING)
stadef DeptSchema =
Schema_cons (DeptID_attr,
Schema_cons (DeptName_attr,
Schema_nil ()))

val deptTable =
list2Table (
  $list{Row DeptSchema}(
    R (int2datavalue (1), R (string2datavalue("Maint"),  EmptyRow ($list{int}(0)))),
    R (int2datavalue (2), R (string2datavalue("Ops"), EmptyRow ($list{int}(1))))
  )
)

stadef EmployeeDeptSchema =
Schema_cons (EmployeeLastName_attr,
Schema_cons (EmployeeFirstName_attr,
Schema_cons (EmployeeDeptID_attr,
Schema_cons (DeptID_attr,
Schema_cons (DeptName_attr,
Schema_nil ())))))

stadef EmployeeDeptSchemaNoID =
Schema_cons (EmployeeLastName_attr,
Schema_cons (EmployeeFirstName_attr,
Schema_cons (DeptID_attr,
Schema_cons (DeptName_attr,
Schema_nil ()))))

//

stadef Grading_grade = "grade"
stadef Grading_gradeAttr = Attr (Grading_grade, NAT)
stadef GradingSchema =
Schema_cons (Attr ("last", STRING),
Schema_cons (Attr ("first", STRING),
Schema_cons (Attr ("year", NAT),
Schema_cons (Grading_gradeAttr,
Schema_cons (Attr ("major", BOOL),
Schema_nil ())))))

val gradingTable =
list2Table (
  $list{Row GradingSchema}(
    R (string2datavalue ("Weirich"), R (string2datavalue("S"), R (int2datavalue(12), R (int2datavalue(3), R (bool2datavalue(false), EmptyRow ($list{int}(0))))))),
    R (string2datavalue ("Eisenberg"), R (string2datavalue("R"), R (int2datavalue(10), R (int2datavalue(4), R (bool2datavalue(true), EmptyRow ($list{int}(1)))))))
  )
)

fun
print_grading (r: Row GradingSchema): void = let
  val+ R (last, R (first, R (year, R (grade, R (major, EmptyRow _))))) = r
  
  var last = last
  val last = datavalue_get_string (last)
  var first = first
  val first = datavalue_get_string (first)
  var year = year
  val year = datavalue_get_int (year)
  var grade = grade
  val grade = datavalue_get_int (grade)
  var major = major
  val major = datavalue_get_bool (major)
  
  val () = println!("last = ", last, ", first = ", first, ", year = ", year, ", grade = ", grade, ", major = ", major)
in
end

fun
print_EmployeeDeptSchema (r: Row EmployeeDeptSchema): void = let
  val+ R (lastname, R (firstname, R (empdeptid, R (deptid, R (deptname, EmptyRow _))))) =r

  var lastname = lastname
  val lastname = datavalue_get_string (lastname)
  var firstname = firstname
  val firstname = datavalue_get_string (firstname)
  var empdeptid = empdeptid
  val empdeptid = datavalue_get_int (empdeptid)
  var deptid = deptid
  val deptid = datavalue_get_int (deptid)
  var deptname = deptname
  val deptname = datavalue_get_string (deptname)
  
  val () = println!("firstname = ", firstname, ", lastname = ", lastname, ", empdeptid = ", empdeptid, ", deptid =", deptid, ", deptname = ", deptname)
in
end

fun
print_EmployeeDeptSchemaNoID (r: Row EmployeeDeptSchemaNoID): void = let
  val+ R (lastname, R (firstname, R (deptid, R (deptname, EmptyRow _)))) =r

  var lastname = lastname
  val lastname = datavalue_get_string (lastname)
  var firstname = firstname
  val firstname = datavalue_get_string (firstname)
  var deptid = deptid
  val deptid = datavalue_get_int (deptid)
  var deptname = deptname
  val deptname = datavalue_get_string (deptname)
  
  val () = println!("firstname = ", firstname, ", lastname = ", lastname, ", deptid =", deptid, ", deptname = ", deptname)
in
end

(* ****** ****** *)

implement main0 () = let
  // exactly one unsolved constraint
  prval pf_grade_in_gradingSchema = InTail (InTail (InTail (InElt {Grading_grade,NAT}))) : InProof (Grading_grade, NAT, GradingSchema, 3)

  val ra1 =
    RAselect (LessThan (Element (pf_grade_in_gradingSchema | 3), Lit (int2datavalue 4)),
    RAread (gradingTable))

  val gradingTable1 = list2Table (query (ra1))

  val () = println!("query result:")
  val () = Table_foreach (gradingTable1, lam (x) => print_grading (x))

  val () = println!("various debug output")
  val () = Table_foreach (gradingTable, lam (x) => print_grading (x))

(*  
  // this breaks all of our stuff...
  // can we get by without it? can we use Z3 instead to solve these constraints?
  // the overall approach seems sound!
  extern praxi neq1 : () -<prf> [eq_string_string (lab_deptid, lab_firstname)] void
  prval () = neq1 ()
  prval () = () : [eq_string_string (lab_deptid, lab_firstname)] void

  prval attr_not_in1 = AttrNotIn_nil () : AttrNotIn (EmployeeDeptID_attr, Schema_nil, true)
  prval attr_not_in2 = AttrNotIn_cons (attr_not_in1) //: AttrNotIn (EmployeeDeptID_attr, Schema_cons (EmployeeFirstName_attr, Schema_nil), true)
*)
  prval pf_emp_dept_disj = __trustme () where {
      extern prfun __trustme (): Schema_disjoint (EmployeeSchema, DeptSchema, true)
  }
  prval pf_emp_dept_app = __trustme () where {
    extern prfun __trustme (): Append (EmployeeSchema, DeptSchema, EmployeeDeptSchema)
  }
  // exactly one unsolved constraint
  prval pf_deptid_in_EmployeeDeptSchema = (InTail (InTail (InElt {lab_deptid,NAT}))) : InProof (lab_deptid, NAT, EmployeeDeptSchema, 2)
  prval pf_dept_in_EmployeeDeptSchema = (InTail (InTail (InTail (InElt {lab_id,NAT})))) : InProof (lab_id, NAT, EmployeeDeptSchema, 3)

  // a query involving a theta-join (aka: cross-product followed by selection)
  val ra2 = RAjoin (pf_emp_dept_disj, pf_emp_dept_app |
    RAread (employeeTable), RAread (deptTable),
    Equals (Element (pf_deptid_in_EmployeeDeptSchema | 2),
            Element (pf_dept_in_EmployeeDeptSchema | 3)))
  val ra2_result = list2Table (query (ra2))

  val () = println!("join result:")
  val () = Table_foreach (ra2_result, lam (x) => print_EmployeeDeptSchema (x))

  prval pf_lastname_in_EmployeeDeptSchema = InElt() : InProof (lab_lastname, STRING, EmployeeDeptSchema, 0)
  prval pf_firstname_in_EmployeeDeptSchema = InTail (InElt ()) : InProof (lab_firstname, STRING, EmployeeDeptSchema, 1)
  prval pf_deptid_in_EmployeeDeptSchema = InTail (InTail (InTail (InElt {lab_id,NAT}()))) : InProof (lab_id, NAT, EmployeeDeptSchema, 3)
  prval pf_deptname_in_EmployeeDeptSchema = InTail (InTail (InTail (InTail (InElt ())))) : InProof (lab_deptname, STRING, EmployeeDeptSchema, 4)

  val ra2_subset =
    SubsetCons (pf_lastname_in_EmployeeDeptSchema | 0,
    SubsetCons (pf_firstname_in_EmployeeDeptSchema | 1,
    SubsetCons (pf_deptid_in_EmployeeDeptSchema | 3,
    SubsetCons (pf_deptname_in_EmployeeDeptSchema | 4,
    SubsetEmpty ()))))
      : SubsetProof (EmployeeDeptSchemaNoID, EmployeeDeptSchema)

  val ra3 = RAproject (ra2_subset, RAread (ra2_result))
  val ra3_result = list2Table (query (ra3))
  val () = println!("projection result:")
  val () = Table_foreach (ra3_result, lam (x) => print_EmployeeDeptSchemaNoID (x))
in
print"Hello World!\n"
end
