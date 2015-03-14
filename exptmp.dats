(*
** Expression templates in ATS2
**
** based on the article:
** http://www.angelikalanger.com/Articles/Cuj/ExpressionTemplates/ExpressionTemplates.htm
**
** Author: Artyom Shalkhakov
** Date: Mar 14, 2015
** License: Public Domain
**
*)

#include
"share/atspre_staload.hats"

staload UN = "prelude/SATS/unsafe.sats"

(*

// from http://www.angelikalanger.com/Articles/Cuj/ExpressionTemplates/ExpressionTemplates.htm
template <size_t N, class T>
class DotProduct  {
public:
  static T eval(T* a, T* b)
  { return  DotProduct<1,T>::eval(a,b) 
          + DotProduct<N-1,T>::eval(a+1,b+1); 
  }
}; 

template <class T>
class DotProduct<1,T> {
public:
  static T eval(T* a, T* b)
  { return ( *a ) * ( *b ); }
}; 

*)

abstype Z
abstype S(type)

dataprop
tieq (type, int) =
| TIEQZ(Z, 0)
| {t:type}{n:nat} TIEQS(S(t), n+1) of tieq(t, n)

(* ****** ****** *)

// interface
extern
fun{T:t@ype}{N:type}
DotProduct_eval {n:nat} (pf: tieq (N, n) | &RD(@[T][n]), &RD(@[T][n])): T

// implementation
implement(T)
DotProduct_eval<T><Z> (pf | x, y) = gnumber_int<T> (0)
implement(T,N)
DotProduct_eval<T><S(N)> {n} (pf | x, y) = let
  prval TIEQS(pf) = pf
  val px = addr@(x)
  val py = addr@(y)
  prval pfxarr = view@(x)
  prval (pfxat, pfxarr1) = array_v_uncons (pfxarr)
  prval pfyarr = view@(y)
  prval (pfyat, pfyarr1) = array_v_uncons (pfyarr)
  val s = gmul_val<T> (!px, !py)
  val px_1 = ptr1_succ<T> (px)  
  val (pfxarr1 | px_1) = viewptr_match (pfxarr1 | px_1)
  val py_1 = ptr1_succ<T> (py)  
  val (pfyarr1 | py_1) = viewptr_match (pfyarr1 | py_1)
  val res = DotProduct_eval<T><N> (pf | !px_1, !py_1)
  prval () = view@(x) := array_v_cons (pfxat, pfxarr1)
  prval () = view@(y) := array_v_cons (pfyat, pfyarr1)
in
  gadd_val<T> (s, res)
end

(* ****** ****** *)

extern
prfun
mk_tieq3 (): tieq (S(S(S(Z))), 3)

local
  var X = @[double][3](1.0, 1.0, 0.0)
  var Y = @[double][3](1.0, 1.0, 0.0)
  val dot = DotProduct_eval<double><S(S(S(Z)))> (mk_tieq3 () | X, Y)
  val () = println! ("dot = ", dot)
in
// nothing
end

(* ****** ****** *)

// the next example given by the article can be easily solved
// using a "finally tagless" interpreter

(*
extern
fun{T:t@ype}{E:type}
Interpreter_eval {e:exp} (pf: expeq (E, e) | T): T
*)
extern
fun{T:t@ype}
Interpreter_lit (x: T): T
extern
fun{T:t@ype}
Interpreter_add (x: T, y: T): T
extern
fun{T:t@ype}
Interpreter_mul (x: T, y: T): T

implement{T}
Interpreter_lit (x) = x
implement{T}
Interpreter_add (x, y) = gadd_val<T> (x, y)
implement{T}
Interpreter_mul (x, y) = gmul_val<T> (x, y)

fun someFunction(x: double) = let
  val expr = Interpreter_mul<double> (
    Interpreter_add<double> (Interpreter_lit<double> (x), Interpreter_lit<double> (2.0))
    , Interpreter_lit<double> (3.0))
in
  println!("someFunction = ", expr)
end

val () = someFunction (3.8)

(* ****** ****** *)

(*

// AS: I'm not sure this works... the article doesn't give a full
// listing

class Literal {
public:   Literal(double v) : _val(v) {}
          double eval(double) const { return _val; }
private:  const double _val;
};

template<class T>
class Identity {
public:   T eval(T d) const { return d; }
};

template <class ExprT1,class ExprT2, class BinOp>
class BinExpr {
   exprTraits<ExprT1>::expr_type _expr1;
   exprTraits<ExprT2>::expr_type _expr2;
   BinOp  _op;
public:
   BinaryExpr(ExprT1 e1, ExprT2 e2,BinOp op=BinOp())
      : _expr1(e1),_expr2(e2),_op(op) {} 
   double eval(double d) const 
          { return _op(_expr1.eval(d),_expr2.eval(d)); }
};

template  <class ExprT>
UnaryExpr<ExprT,double( * )(double)>
sqrt(const ExprT& e) 
{return UnaryExpr<ExprT,double( * )(double)>(e,::std::sqrt);}

template  <class ExprT>
UnaryExpr<ExprT,double( * )(double)>
exp(const ExprT& e) 
{ return UnaryExpr<ExprT,double( * )(double)>(e,::std::exp); } 

template <class ExprT>
double integrate (ExprT e,double from,double to,size_t n)
{  double sum=0, step=(to-from)/n;
   for (double i=from+step/2; i<to; i+=step)
       sum+=e.eval(i);
   return step*sum;
}

template <class ExprT>
double eval(ExprT e) { return e.eval(); }

void someFunction() {
Identity<double> x;
cout << integrate (x/(1.0+x),1.0,5.0,10) << endl;
}
*)

// NOTE: for static dispatch to work properly,
// types must be pairwise distinct!
// e.g. Tid (represented by int) is not Tconst (represented by double)
// likewise, Tadd and Tdiv are non-compatible records

extern
fun{T:t@ype}
eval (x: &T, i: double): double

(* ****** ****** *)

abst@ype Tid

local

assume Tid = int

in // in of [local]

fun Eid (): Tid = 0
implement
eval<Tid> (x, i) = i

end // end of [local]

(* ****** ****** *)

abst@ype Tconst

local
//
assume Tconst = double
//
in // in of [local]
//
fun Econst (x: double): Tconst = x
//
implement
eval<Tconst> (x, i) = x
//
end // end of [local]

(* ****** ****** *)

abst@ype Tadd (t@ype, t@ype)

local
//
typedef Tadd_ (a:t@ype, b:t@ype) = @{summand0=a, summand1=b}
assume Tadd (a:t@ype, b:t@ype) = Tadd_ (a, b)
//
in // in of [local]
//
fun{a,b:t@ype}
Eadd (e0: a, e1: b): Tadd (a, b) =
  @{summand0=e0, summand1=e1}
//
implement(E1,E2)
eval<Tadd(E1,E2)> (x, i) = let
  val e0 = eval<E1> (x.summand0, i)
  val e1 = eval<E2> (x.summand1, i)
in
  e0 + e1
end
//
end // end of [local]

(* ****** ****** *)

abst@ype Tdiv (t@ype, t@ype)

local
//
typedef Tdiv_ (a:t@ype, b:t@ype) = @{numerator=a, denumerator=b}
assume Tdiv (a:t@ype, b:t@ype) = Tdiv_ (a, b)
//
in // in of [local]
//
fun{a,b:t@ype}
Ediv (e0: a, e1: b): Tdiv (a, b) =
  @{numerator=e0, denumerator=e1}
//
implement(E1,E2)
eval<Tdiv(E1,E2)> (x, i) = let
  val e0 = eval<E1> (x.numerator, i)
  val e1 = eval<E2> (x.denumerator, i)
in
  e0 / e1
end // end of [eval]
//
end // end of [local]

(* ****** ****** *)

fun{T:t@ype}
integrate (e: &T, from: double, to: double, n: int): double = let
  var sum: double = 0.0
  var step: double = (to-from) / g0int2float_int_double(n)
  var i: double = from + step / 2.0
in
  while (i < to) {
    val v = eval<T>(e, i)
    // DEBUG
    // val () = println! ("value for ", i, " is ", v)
    val () = sum := sum + v
    val () = i := i + step
  };
  step * sum
end


val () = () where {
  // we just copy values (the C++ version stores references)
  var x = Eid ()
  var e = Ediv (x, Eadd (Econst 1.0, x))
  // the idea behind C++ expression templates
  // seems to be that all case analysis
  // is performed at compile-time
  val () = println! ("integrate = ", integrate<Tdiv (Tid, Tadd (Tconst, Tid))> (e, 1.0, 5.0, 100))
}


(* ****** ****** *)

implement main0 () = ()

(* ****** ****** *)
