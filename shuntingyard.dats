#include
"share/atspre_staload.hats"

(* ****** ****** *)
(* operator interface *)

datatype assoc = ASSOCnone | ASSOCleft | ASSOCright
extern
fun
eq_assoc_assoc (assoc, assoc):<> bool
overload = with eq_assoc_assoc
extern
fun
ne_assoc_assoc (assoc, assoc):<> bool
overload <> with ne_assoc_assoc

abstype operator = ptr
extern
fun
operator_make (label: string, a: assoc, precedence: Nat): operator
extern
fun
operator_label (operator): string
extern
fun
operator_prec (operator): Nat
extern
fun
operator_assoc (operator): assoc
extern
fun
operator_fprint (FILEref, operator): void

(* ****** ****** *)
// operator implementation

local

// need a hash table (string->operator info)
// need methods for populating it
datatype OPERATOR = OPERATOR of (string, assoc, Nat)
assume operator = OPERATOR

in

implement
eq_assoc_assoc (l, r) =
  case+ (l, r) of
  | (ASSOCnone (), ASSOCnone ()) => true
  | (ASSOCleft (), ASSOCleft ()) => true
  | (ASSOCright (), ASSOCright ()) => true
  | (_, _) => false

implement
ne_assoc_assoc (l, r) = ~(eq_assoc_assoc (l, r))

implement
operator_make (label, a, p) = OPERATOR (label, a, p)

implement
operator_label (o) = let
  val+ OPERATOR (lab, _, _) = o
in
  lab
end

implement
operator_prec (o) = let
  val+ OPERATOR (lab, a, p) = o
in
  p
end

implement
operator_assoc (o) = let
  val+ OPERATOR (lab, a, p) = o
in
  a
end

implement
operator_fprint (out, o) = {
  val+ OPERATOR (lab, a, p) = o
  (*
  val s =
    (case+ a of
    | ASSOCnone () => "no"
    | ASSOCleft () => "lf"
    | ASSOCright () => "rg"): string
  *)
  val () = fprint!(out, lab)
  (*
  val () = fprint!(out, "(")
  val () = fprint!(out, s)
  val p = (g0ofg1)p
  val () = fprint!(out, ",", p, ")")
  *)
}

end

(* FIXME: HACK *)
overload fprint with operator_fprint

(* ****** ****** *)
(* token interface *)

%{^

typedef enum {
    NIL = 0,
    OPER = 1,
    NUMBER = 2,
    COMMA = 3,
    LPAR = 4,
    RPAR = 5,
    FUNCALL = 6
} CTOKEN_ENUM;
typedef struct {
  CTOKEN_ENUM tt;
  union {
      atstype_boxed oper;
      int num;
  } tv;
} CTOKEN_TYPE;

ATSinline()
CTOKEN_TYPE TOKEN_NUMBER(atstype_int x) {
  CTOKEN_TYPE res;
  res.tt = NUMBER;
  res.tv.num = x;
  return res;
}
ATSinline()
CTOKEN_TYPE TOKEN_LPAR() {
    CTOKEN_TYPE res;
    res.tt = LPAR;
    return res;
}
ATSinline()
CTOKEN_TYPE TOKEN_RPAR() {
    CTOKEN_TYPE res;
    res.tt = RPAR;
    return res;
}
ATSinline()
CTOKEN_TYPE TOKEN_OPERATOR(atstype_boxed oper) {
    CTOKEN_TYPE res;
    res.tt = OPER;
    res.tv.oper = oper;
    return res;
}

ATSinline()
atstype_bool TOK_IS_OPER (CTOKEN_TYPE tok) {
    return tok.tt == OPER ? atsbool_true : atsbool_false;
}
ATSinline()
atstype_bool TOK_IS_NUMBER(CTOKEN_TYPE tok) {
    return tok.tt == NUMBER ? atsbool_true : atsbool_false;
}
ATSinline()
atstype_bool TOK_IS_COMMA(CTOKEN_TYPE tok) {
    return tok.tt == COMMA ? atsbool_true : atsbool_false;
}
ATSinline()
atstype_bool TOK_IS_LPAR(CTOKEN_TYPE tok) {
    return tok.tt == LPAR ? atsbool_true : atsbool_false;
}
ATSinline()
atstype_bool TOK_IS_RPAR(CTOKEN_TYPE tok) {
    return tok.tt == RPAR ? atsbool_true : atsbool_false;
}
ATSinline()
atstype_bool TOK_IS_FUNCALL(CTOKEN_TYPE tok) {
    return tok.tt == FUNCALL ? atsbool_true : atsbool_false;
}
ATSinline()
atstype_int TOK_GET_NUMBER (CTOKEN_TYPE tok) {
    return tok.tv.num;
}
ATSinline()
atstype_boxed TOK_GET_OPERATOR (CTOKEN_TYPE tok) {
    return tok.tv.oper;
}

%}

#define OPER 1
#define NUMBER 2
#define COMMA 3
#define LPAR 4
#define RPAR 5
#define FUNCALL 6

abst@ype token (int) = $extype"CTOKEN_TYPE"
typedef Token = [tag:int] token(tag)

extern
fun
token_number (int): token (NUMBER) = "ext#TOKEN_NUMBER"
extern
fun
token_lpar (): token (LPAR) = "ext#TOKEN_LPAR"
extern
fun
token_rpar (): token (RPAR) = "ext#TOKEN_RPAR"
extern
fun
token_operator (operator): token (OPER) = "ext#TOKEN_OPERATOR"


extern
fun
token_is_operator {i:int} (token(i)): bool(i==OPER) = "ext#TOK_IS_OPER"
extern
fun
token_is_number {i:int} (token(i)): bool(i==NUMBER) = "ext#TOK_IS_NUMBER"
extern
fun
token_is_comma {i:int} (token(i)): bool(i==COMMA) = "ext#TOK_IS_COMMA"
extern
fun
token_is_lpar {i:int} (token(i)): bool(i==LPAR) = "ext#TOK_IS_LPAR"
extern
fun
token_is_rpar {i:int} (token(i)): bool(i==RPAR) = "ext#TOK_IS_RPAR"
extern
fun
token_is_funcall {i:int} (token(i)): bool(i==FUNCALL) = "ext#TOK_IS_FUNCALL"
extern
fun
token_get_number (token(NUMBER)): int = "ext#TOK_GET_NUMBER"
extern
fun
token_get_operator (token(OPER)): operator = "ext#TOK_GET_OPERATOR"

extern
fun
token_fprint (out: FILEref, Token): void
overload fprint with token_fprint
extern
fun
token_print (Token): void
overload print with token_print

(* ****** ****** *)
(* token implementation *)

implement
token_fprint (out, tok) =
  if token_is_operator (tok) then {
    val oper = token_get_operator (tok)
    val () = fprint!(out, oper)
  } else if token_is_number (tok) then {
    val num = token_get_number (tok)
    val () = fprint!(out, num)
  } else if token_is_comma (tok) then {
    val () = fprint!(out, ",")
  } else if token_is_lpar (tok) then {
      val () = fprint!(out, "(")
  } else if token_is_rpar (tok) then {
      val () = fprint!(out, ")")
  }
  else fprint!(out, "NIL()")

implement
token_print (tok) = token_fprint (stdout_ref, tok)

(* ****** ****** *)

(* will not return a token if EOF *)
extern
fun{}
tokenizer_get_token (&Token? >> opt (Token, b)): #[b:bool] bool b
extern
fun{}
tokenizer_emit_token (&Token): void

extern
fun{}
shunting_yard (): void

staload "libats/SATS/stkarray.sats"
staload _(*anon*) = "libats/DATS/stkarray.dats"

extern
fun{a:t@ype}
stkarray_peek_top
  {m,n:int | n > 0}
(
  stk: !stkarray (INV(a), m, n) >> stkarray (a, m, n)
) :<!wrt> (a) // endfun

implement{a}
stkarray_peek_top {m,n} (stk) = let
  prval () = lemma_stkarray_param (stk)
  val res = stkarray_takeout<a> (stk)
  val () = stkarray_insert<a> (stk, res)
in
  res
end

implement{}
shunting_yard () = {
  vtypedef opstack = stkarray (Token)

  fun
  pop_until_lpar (opstack: !opstack >> _): bool =
    if stkarray_isnot_nil (opstack) then let
      var tok = stkarray_peek_top<Token> (opstack)
    in
      if :(opstack: opstack) => token_is_lpar (tok) then let
        val notfull = stkarray_isnot_full (opstack)
        val () = assert_errmsg (notfull, "stack overflow")
        val () = stkarray_insert<Token> (opstack, tok)
      in
        true
      end else let
        var tok = stkarray_takeout<Token> (opstack)
        val () = tokenizer_emit_token (tok)
      in
        pop_until_lpar (opstack)
      end
    end else false
  // end of [pop_until_lpar]

  fun
  shift (opstack: !opstack >> _, o1: operator): void =
    if stkarray_isnot_nil (opstack) then let
      //var tok = stkarray_peek_top<Token> (opstack)
      var tok = stkarray_takeout<Token> (opstack)
    in
      if token_is_operator (tok) then let
        val o2 = token_get_operator (tok)
        val r = operator_assoc (o1) = ASSOCleft && operator_prec (o1) <= operator_prec (o2)
        val q = operator_assoc (o2) = ASSOCright && operator_prec (o1) < operator_prec (o2)
        val p = r || q
      in
        if p then let
          val () = tokenizer_emit_token (tok)
        in
          shift (opstack, o1)
        end else let
          val notfull = stkarray_isnot_full (opstack)
          val () = assert_errmsg (notfull, "stack overflow")
          val () = stkarray_insert<Token> (opstack, tok)
        in
          (*empty*)
        end
      end else let
        val notfull = stkarray_isnot_full (opstack)
        val () = assert_errmsg (notfull, "stack overflow")
        val () = stkarray_insert<Token> (opstack, tok) (* token is not an operator *)
      in
      end
    end
  // end of [shift]

  fun
  clear (opstack: opstack): void = let
    prval () = lemma_stkarray_param (opstack)
  in
    if stkarray_isnot_nil (opstack) then let
      var tok = stkarray_takeout<Token> (opstack)
      (*
      val () = println!("clearing token: ")
      val () = token_print (tok)
      *)
      val ispar = token_is_lpar (tok) || token_is_rpar (tok)
      (*
      val () = println!("is parentheses: ", ispar)
      *)
      val () = assert_errmsg (~ispar, "mismatched parens 1")
      val () = tokenizer_emit_token (tok)
    in
      clear (opstack)
    end else stkarray_free_nil (opstack)
  end // end of [clear]

  fun
  loop (opstack: opstack): void = let
    var tok : Token
    val b = tokenizer_get_token (tok)
  in
    if :(tok: Token?) => b then let
      prval () = opt_unsome (tok)
      val () =
          if token_is_number (tok) then tokenizer_emit_token (tok)
          else if token_is_funcall (tok) then tokenizer_emit_token (tok)
          else if token_is_comma (tok) then let
            val lp = pop_until_lpar (opstack)
            val () = assert_errmsg (lp, "misplaced separator or mismatched parentheses")
          in
            (*empty*)
          end else if token_is_operator (tok) then let
            val o1 = token_get_operator (tok)
            val () = shift (opstack, o1)
            (*
            val () = println!("shifted!")
            *)
            val notfull = stkarray_isnot_full (opstack)
            val () = assert_errmsg (notfull, "stack overflow")
            val () = stkarray_insert<Token> (opstack, tok)
          in
            (*empty*)
          end else if token_is_lpar (tok) then let
            val notfull = stkarray_isnot_full (opstack)
            val () = assert_errmsg (notfull, "stack overflow")
            val () = stkarray_insert<Token> (opstack, tok)
            //val () = tokenizer_emit_token (tok)
          in
          end else if token_is_rpar (tok) then let
            (*
            val () = println!("got to rpar")
            *)
            val lp = pop_until_lpar (opstack)
            (*
            val () = println!("popped until lpar")
            *)
            val () = assert_errmsg (lp, "mismatched parentheses")
            val-true = stkarray_isnot_nil (opstack) // implied by lp=true!
            val lpar_tok = stkarray_takeout<Token> (opstack) // pop the lpar
            (*
            val () = println!("popped the token: ", lpar_tok)
            *)
          in
            if stkarray_isnot_nil (opstack) then let
              var tok = stkarray_takeout<Token> (opstack)
            in
              if token_is_funcall (tok) then tokenizer_emit_token (tok)
            end
          end else tokenizer_emit_token (tok)
      // end of [val]
    in
      loop (opstack)
    end else let
      prval () = opt_unnone (tok)
    in
      clear (opstack)
    end
  end

  #define OPSTACK_SIZE 512
  val opstack = stkarray_make_cap<Token> ((i2sz)OPSTACK_SIZE)
  val () = loop (opstack)
}

(* ****** ****** *)

fun
test_drive (inp: string): void = let
  val () = println!("input: ", inp)

  var str = inp: string
  prval pf_str = view@ (str)

  // TODO: move into a proper lookup table
  val op_pow = operator_make ("^", ASSOCright, 4)
  val op_mul = operator_make ("*", ASSOCleft, 3)
  val op_div = operator_make ("/", ASSOCleft, 3)
  val op_sum = operator_make ("+", ASSOCleft, 2)
  val op_sub = operator_make ("-", ASSOCright, 2)

  implement
  tokenizer_get_token<> (tok) = let
    prval (pf_res, fpf) = decode($vcopyenv_v(pf_str))
    val s = (g1ofg0)str
    prval () = lemma_string_param (s)
    prval () = fpf (pf_res)
  in
    if string_isnot_empty (s) then let
      val c = string_head (s)
      (*
      val () = println!("input char:", c)
      *)
      prval (pf_res, fpf) = decode($vcopyenv_v(pf_str))
      val () = str := (g0ofg1)(string_tail s)
      prval () = fpf (pf_res)
    in
      if c = '\n' then tokenizer_get_token<> (tok) // skip!
      else let
        val () = tok := (
          if isdigit c then let
            val n = char2int0 c
            val n0 = char2int0 '0'
            val n = n - n0
          in
            token_number (n)
          end else if c = '\(' then token_lpar ()
          else if c = ')' then token_rpar ()
          else if c = '^' then token_operator (op_pow)
          else if c = '*' then token_operator (op_mul)
          else if c = '/' then token_operator (op_div)
          else if c = '+' then token_operator (op_sum)
          else if c = '-' then token_operator (op_sub)
          else let
            val () = println! ("unknown character: ", c)
            val () = assert_errmsg (false, "unrecognized input character")
          in
            token_lpar () // arbitrary
          end
        ) (* end of [val] *)
        prval () = opt_some (tok)
      in
        true
      end
    end else let
      prval () = opt_none (tok)
    in
      false
    end
  end // end of [let]

  var ntokens = 0 : int
  prval pf_ntokens = view@ (ntokens)
  implement
  tokenizer_emit_token<> (tok) = {
    prval (pf, fpf) = decode($vcopyenv_v(pf_ntokens))
    val () = if isgtz(ntokens) then print!(" ")
    val () = ntokens := succ(ntokens)
    prval () = fpf (pf)
    val () = print! (tok)
  }

  val () = shunting_yard<> ()
  val () = println!()

  prval () = view@ (str) := pf_str
  prval () = view@ (ntokens) := pf_ntokens
in
end

(* ****** ****** *)

staload "libc/SATS/stdio.sats"
staload
UN="prelude/SATS/unsafe.sats"

fun loop
  {sz:pos} (
  inp: FILEref
, buf: &bytes(sz)? >> _
, sz: int sz
) : void = let
  val p = fgets0 (buf, sz, inp)
in
  if p > 0 then let // p=addr@(buf) or NULL
    val () = test_drive ($UN.cast{string}(p))
  in
    loop (inp, buf, sz)
  end else () // end of [if]
end // end of [loop]

fun
read_from_stdin (): void = {
  #define BUFSZ 128
  var buf = @[byte][BUFSZ]()
  val () = loop (stdin_ref, buf, BUFSZ)
}

implement
main0 () = let
  val () = println!("test 1")
  val () = test_drive("3+4")
  
  val () = println!("test 2")
  val () = test_drive("2+2*2")
  
  val () = println!("test 3")
  val () = test_drive("(2+2)*2")

  val () = println!("test 4")
  val () = test_drive("3+4*2/(1-5)^2^3")
  
  val () = println!("Try your own expression below! Press Ctrl-C to exit.")
  val () = read_from_stdin ()
in

end