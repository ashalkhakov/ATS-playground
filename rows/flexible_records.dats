staload
_ = "prelude/DATS/list.dats"
staload
_ = "prelude/DATS/reference.dats"
staload
_ = "prelude/DATS/pointer.dats"

implement
fprint_ref<string> (out, x) = fprint (out, x)

abstype Relation (b:t@ype) = ptr

assume Relation (a:t@ype) = ref (List (a))

(*

see also: http://cs.brynmawr.edu/~rae/papers/2012/singletons/paper.pdf
- kind of similar to what we want to do here

// what if it failed to convert? need easy api for that
// - convert from raw DB value to host representation
// - convert from host representation to raw DB value
fun{a:t@ype}
dbtype2string (&a >> _, res: &ptr >> Strptr1): void
fun{a:t@ype}
string2dbtype (Strptr1 >> _, &a? >> _): void
*)
// we can enrich these with default values...
// and also with nulls that are explicitly typed
abst@ype PI (a:t@ype, b:t@ype) = @{idx= int, get= ptr, set= ptr(*, def= ptr*)} // you can extract [b] out of [a]
extern
fun{a:t@ype}{b:t@ype}
PI_get (&a >> _, PI (INV(a), INV(b))): b
extern
fun{a:t@ype}{b:t@ype}
PI_set (&a >> _, PI (INV(a), INV(b)), b): void
(*
extern
fun{a:t@ype}{b:t@ype}
PI_def (PI(INV(a), INV(b))): b // produce a default value
*)

extern
fun{a:t@ype}{b:t@ype}
PI_fprint (FILEref, &a >> _, PI (INV(a), INV(b))): void

overload [] with PI_get
overload [] with PI_set

assume PI (a:t@ype, b:t@ype) = @{idx= int, get= (&a) -> b, set= (&a, b) -> void(*, def= () -> b*)}
implement{a}{b}
PI_get (r, f) = f.get(r)
implement{a}{b}
PI_set (r, f, x) = f.set(r, x)
(*
implement{a}{b}
PI_def (f) = f.def()*)
implement{a}{b}
PI_fprint (out, r, f) = let
  var tmp = PI_get (r, f)
in
  fprint_ref<b>(out, tmp)
end

(* ****** ****** *)

(*
extern
fun{b:t@ype}
relation_insert (relation(b), &b >> _): void
// insertion:
// - run all before-insert handlers (see if insert should be rejected), possibly updating the row
// - perform the insert (ensure we save the data into our own change log...)
//   - well, this might fail if row is already there...
//   - check non-deferred constraints
// - run all after-insert handlers (these might perform additional changes)
extern
fun{b:t@ype}
relation_update(relation(b), &b >> _): void
extern
fun{b:t@ype}
relation_delete(relation(b), &b >> _): void

// keys of relation / UCs (multiple)
// - what's a key? it's a set of columns of the relation
// foreign keys of relation / RCs
abstype UC (b:t@ype) = ptr // what is it? it's a big function that uses the knowledge of relation's structure
extern
fun{a:t@ype}{b:t@ype}
UC_make (Relation(a), List (PI (INV(a), INV(b)))): UC(a)
// to enforce a UC?
// what else?
*)

(* ****** ****** *)

// what else do you want from a row type?
// - equality/inequality checks (easily check if two rows are equal? not equal?)
// - column defaults (done, all columns have some overridable default value)
// - events? row modified, row created, row deleted / column update handler (e.g. what to do when something changes...)
//   - some of these are specific to tables! so, don't put these into rows!
// - handling of references to other rows / FKs (e.g. want to follow links set by FKs)
// - conversion to/from database representation (list of generic values <-> record) 
// - nullable columns (e.g. unable to extract value... because it isn't present!)
//   - easily solved with more descriptive custom types (e.g. Option(int))
// - complex types -- also solved by host language ATS
(*

conversion from untyped row to typed row
and back!
- e.g. assume that untyped row will be an array of strings
- also assume that each type participating in PI will provide its very
  own functions to read/write its values

*)

typedef Employee = @{ID= int, FirstName=string, LastName=string, EmpDeptID= int}
extern
val employee : Relation (Employee)
extern
fun employee_default (&Employee? >> _): void
extern
val emp_id : PI (Employee, int)
extern
val first_name : PI (Employee, string)
extern
val last_name : PI (Employee, string)
extern
val emp_dept_id : PI (Employee, int)

// need a new type constructor for FKs, and some way to form compound projections
// e.g. project two, three fields out of a record (use a tuple? I think we could build up a tuple!)
(*
extern
val employeeFK1 : reference_constraint (Employee, int, Department, int)
// what's the use of this? operationally?
// 1. given e:Employee, x = e[emp_dept_id] should point to d:Department s.t. x = d[dept_id]
//  -- always check during insert/update
// -- neat as a lookup!
// 2. given d:Department, there exist one or more e:Employee s.t. d[dept_id] = e[works_in]
// -- neet as a way to get all employees of a dept

this is very similar to role-centric view on ORM!
- our PI things --> roles!

now we need to encode object types
- what we do have corresponds mostly to FACT TYPES!

abstype object_type (t@ype) = ptr // identified by value-type
val
Employee : object_type (int) // employee identified by integer ID
val
employee_has_id : fact_type ()
val
employee_has_id_R1 : 

now we need to encode join paths and we're golden!

abstype path = ptr
val path_starts_at : Relation (r) -> path // path starts at this relation
*)

(* ****** ****** *)

implement
emp_id = @{idx= 0, get= lam (r) => r.ID, set= lam (r, x) => r.ID := x(*, def= lam () => 0*)}
implement
first_name = @{idx= 1, get= lam (r) => r.FirstName, set= lam (r, x) => r.FirstName := x(*, def= lam() => ""*)}
implement
last_name = @{idx= 2, get= lam (r) => r.LastName, set= lam (r, x) => r.LastName := x(*, def= lam() => ""*)}
implement
emp_dept_id= @{idx= 3, get= lam (r) => r.EmpDeptID, set= lam (r, x) => r.EmpDeptID := x}

implement
employee_default (r) = let
  val () = r.ID := 0 // PI_def (emp_id)
  val () = r.FirstName := "" // PI_def (first_name)
  val () = r.LastName := "" // PI_def (last_name)
  val () = r.EmpDeptID := 0 // PI_def (emp_dept_id)
in
end

implement // list columns?
employee = ref (list_nil ())

//
typedef Department = @{DeptID= int, DeptName=string}
extern
val department : Relation (Department)
extern
fun department_default (&Department? >> _): void
extern
val dept_id : PI (Department, int)
extern
val dept_name : PI (Department, string)

implement // list columns?
department = ref (list_nil ())

implement
dept_id = @{idx= 0, get= lam (r)=> r.DeptID, set= lam (r, x) => r.DeptID := x(*, def= lam () => 0*)}
implement
dept_name = @{idx= 1, get= lam (r) => r.DeptName, set= lam (r, x) => r.DeptName := x(*, def= lam() => ""*)}

implement
department_default (r) = let
  val () = r.DeptID := 0
  val () = r.DeptName := ""
in
end

// TODO: now, using string2dbtype and dbtype2string
// - implement functions for reading/writing rows to db/to host
// - this should be enough for very simple cases

(*
can we use this knowledge to implement
a no-frills DB Execute/ExecuteQuery support?
- you give your typed row to the system,
- the system marshals it to DB,
- and gives you back results in typed form, again

bind(in/out/twoway, my_pi, value) <-- give the database a reference to your var
*)

(* ****** ****** *)

// for ORM embedding:

(* ****** ****** *)

implement main0 () = let
//
var d1 : Department
val () = department_default (d1)
val () = d1[dept_id] := 1
val () = d1[dept_name] := "Development"
//
var e1 : Employee
// apply defaults to all columns
val () = employee_default (e1)
//
(*
d1 <- context.depts[1]; // get existing from environment.. lookup by key
e1 <- context.employee.new // get it from the environment... from the context
e1[works_in] := d1[dept_id]
e1[first_name] := "Hiroshi"
e1[last_name] := "Miyamoto"

works_in : (Employee,Department) -> Prop // this can later be added to the system
// Prop can be Asserted or Retracted
*)
// set initial values
val () = e1[emp_id] := 1
val () = e1[first_name] := "Hiroshi"
val () = e1[last_name] := "Miyamoto"
val () = e1[emp_dept_id] := d1[dept_id]
//
// get current values and print them
val () = println!("firstname is: ", e1[first_name])
val () = println!("updating ident...")
// mutate the record
val () = e1[emp_id] := 2
val () = println!("ident is now: ", e1[emp_id])
//
val () = print!("testing fprint: last name = ")
val () = PI_fprint (stdout_ref, e1, last_name)
val () = println!()
//
in
print"Hello World!\n"
end