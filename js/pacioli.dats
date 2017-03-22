(*
** Hello, world!
*)

(* ****** ****** *)

#include
"share/atspre_define.hats"
#include
"{$LIBATSCC2JS}/staloadall.hats"

(* ****** ****** *)

staload
"{$LIBATSCC2JS}/SATS/print.sats"

(* ****** ****** *)

#define ATS_MAINATSFLAG 1
#define ATS_DYNLOADNAME "my_dynload"

(* ****** ****** *)

abstype pac = ptr
extern
fun
pac_nat_nat (dbt:Nat, crd:Nat): pac
extern
fun
pac_zero (n:Nat): pac
extern
fun
add_pac_pac (pac, pac): pac
extern
fun
sub_pac_pac (pac, pac): pac
extern
fun
inv_pac (pac): pac
extern
fun
eq_pac_pac (pac, pac): bool
extern
fun
print_pac (pac): void

overload print with print_pac

(* ****** ****** *)

local

assume pac = $tup(Nat, Nat)

in

implement
pac_nat_nat (dbt, crd) = $tup (dbt, crd)

implement
pac_zero (n) = $tup (n, n)

implement
add_pac_pac (x, y) = $tup (x.0+y.0, x.1+y.1)

implement
sub_pac_pac (x, y) = $tup (x.0+y.1, x.1+y.0)

implement
inv_pac (x) = $tup (x.1, x.0)

implement
eq_pac_pac (x, y) = (x.0 + y.1 = x.1 + y.0)

implement
print_pac (x) = {
  val () = print!(x.0, "//", x.1)
}

end

(* ****** ****** *)

// this requires some DSL... dammit
// e.g. we could introduce some abstract types for every row type...
// - this would help with getters/setters (isolate some logic)
// - every row should still be linked to its context, somehow
typedef
txn = $rec{
  id= int,
  title= string,
  date= string, // TODO: date data type!
  descr= string,
  class_code= string,
  balance= pac // derived & stored
}
typedef
txn_line = $rec{
  id= int,
  txn_id= int, // reference to txn
  account_code= string,
  amount= pac
}

typedef
account = $rec{
  id= int,
  code= string,
  descr= string
}

// where's my D4 when you need it???
// what if we just take a step back and use fact types that can be asserted/retracted?
// e.g. new fact type: assert account has ID 1, assert account(1) has description 'Assets'
(*
abstype etype (t@ype, int) = ptr
abstype fact = ptr

abst@ype txn = ptr

fun
txn : int(i) -> etype (txn, i)
fun
description : (txn(i), string) -> fact
fun
code : (txn(i), string) -> fact

context.assert($list(
  exists(Account(1)),
  has_Description(Account(1), "ASSETS")
));

// what are txn, txn_line?
// txn: etype (int)
// txn_line: etype (int)

context.assert( // assert : List (fact) -> void
  exists (txn(1)), // txn : int-> txn exists: txn -> fact
  has_description(txn(1), "test txn"), // has_description : (txn, string) -> fact
  has_code(txn(1), "foobar"), // has_code : (txn, string) -> fact
  exists (txn_line(1)),
  exists (txn_line(2)),
  is_of(txn_line(1), txn(1)), // is_of : (txn_line, txn)->fact
  is_of(txn_line(2), txn(1)),
  for_account(txn_line(1), "ASSETS"), // for_account : (txn_line, txn)->fact
  for_account(txn_line(2), "LIABILITIES"),
  amounts(txn_line(1), pac_make(10, 0)), // amounts : (txn_line, pac) -> fact
  amounts(txn_line(2), pac_make(0, 10))
)

SQL reading of the above?
- well, I don't know what it will be
- but here is also the best place to check constraints
  - what constraints do we want to enforce?
  - internal UC, external UC, integrity between the fact types

so, every fact type/predicate is represented by a strange function that builds up some data, which we can plug into a transaction script
- this transaction script can be interpreted by the context, which will build up corresponding SQL... that's the plan
- how to efficiently build up the sql? BTW, entity types can be linear. heh heh.

but what about creating new entities? do we need a new operator in the DSL? instead of exists, above?

let_ new_txn (lam txn1 =>
  $list(
  has_description(txn1, "test txt"),
  has_code(txn1, "foobar"),
  )
)

something like that. basically we want a "let" construct too, and to glue up some atomic assertions as well, into bigger assertions.

this treads into uncharted datalog territory. hmmm. is datalog even suitable for describing business shit?
*)
abstype relation (t@ype) = ptr
abstype ref_constraint (t@ype, t@ype) = ptr

// solution to the uniqueness constraint problem?
// - specific type, e.g. abstype transactions = ptr
// - but we also want to ensure that this specific type shares traits
//   with other relations... somehow

typedef
db_context= $rec{
  // need to pack some constraints here
  // e.g. unique constraint: txn (txn.id)
  transactions= relation (txn),
  transaction_lines= relation (txn_line),
  accounts= relation (account),

  // this is more like a function: given txn_line.txn_id, you can obtain txn
  // correspondingly, given txn.id, you can obtain all txn_line records
  transaction_line_fk1= ref_constraint (txn_line.txn_id, txn.id)
  // similar
  transaction_line_fk2= ref_constraint (txn_line.acct_code, account.code)
}

// transaction?
// - Transaction J has a Title
// - Transaction J occurred on Date // valid date
// - Transaction J has a Description
// - Line I is part of Transaction J
// - Line I is for Account X
// - Line I amounts to Pacioli X
//
//
// balance of Transaction J? (derived & stored)
//   - sum over forall Line I, if Line I is part of Transaction J then add its amount to balance
//
// Transaction J is balanced means: balance of Transaction J equals 0//0

// every Transaction is balanced => the whole system is balanced
// what's a general ledger? it's a set of account + their current balances (derived&stored)
// e.g. http://www.leoisaac.com/fin/fin049.htm
//
// where are the accounts defined? in the chart of accounts
// - Account X is active/passive
// - Account X is subaccount of at most Account Y - tree hierarchy
// note that top-level accounts are dubbed synthetic, and they are usually all derived (e.g. Assets = MyCar + MyHouse, where Assets is thus fully derived and stored)

// after transactions, we need journals
// example txns: http://www.myaccountingcourse.com/accounting-cycle/journal-entries
// basically, every journal groups some transactions, but I don't know how this grouping is established -- looks like it's enough to include a classifier for transactions:
// - Transaction J is classified into Journal X

// after we create transactions on journals, we have to POST the transactions to ledgers
// -  The purpose of the general ledger is to summarise the monthly postings from the Journal Books throughout the year. The ledger will be set out in a particular order.  For example, we may use the order Proprietorship, Assets, Liabilities, Expenses and Revenue that are referred to as PALER order. Definitions for each of these are on page two.
// - so, a ledger will contain SUMMARIZED data, derived from journals; usually, the "posting" is done once a month - but what is posting, then? how to post?
// - is the ledger simply containing summarized data per month, say?

// but what features are to be included? https://www.myob.com/au/accounting-software/essentials -- MYOB is very popular


(* ****** ****** *)
//
extern
fun
hello(): void = "mac#"
implement
hello() = let

  val x = pac_zero (0)
  val y = pac_zero (10)
  val z = add_pac_pac (x, y)
  val-true = eq_pac_pac (x, z) // zero + zero is still a zero!
  
  val () = print(z)
  val () = print_newline ()
  
  val x = pac_nat_nat (10, 0)
  val y = pac_nat_nat (0, 10)
  val z = add_pac_pac (x, y)
  val-true = eq_pac_pac (pac_zero (0), z)
  
  // x-y = x+(-y)
  val z1 = sub_pac_pac (x, y)
  val z2 = add_pac_pac (x, inv_pac (y))
  val () = println!("z1 = ", z1, ", z2 = ", z2)

in
print("Hello, world!")
end
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
