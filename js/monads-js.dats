(*
** Hello, monadic world!
**
** Author: Artyom Shalkhakov
** artyom DOT shalkhakov AT gmail DOT com
**
** Can be run using:
** http://www.ats-lang.org/SERVER/MYCODE/Patsoptaas_serve.php
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

stadef cfun = cfun1
stadef cfun = cfun2

(* ****** ****** *)
// dictionary-based encoding of type-classes

typedef mmonad (m: t@ype -> t@ype) = $rec{
  mretn= {a:t@ype} a -<cloref1> m a,
  mbind= {a,b:t@ype} (m a, (a -<cloref1> m b)) -<cloref1> m b
}

// the passed-in dictionary is akin to a proof attesting
// to the fact that [m] is a monad
extern
val
mmonad_join : {m:t@ype -> t@ype}{a:t@ype}
  (mmonad (m), m (m (a))) -<cloref1> m (a)
extern
val
mmonad_lift : {m:t@ype -> t@ype}{a1,r:t@ype}
  (mmonad (m), m (cfun (a1, r)), m (a1)) -<cloref1> m (r)
extern
val
mmonad_ap : {m:t@ype -> t@ype}{a,b:t@ype} (mmonad (m), m (cfun (a, b)), m (a)) -<cloref1> m (b)

implement
mmonad_join {m}{a} (pfm, ma) = let
  val res = pfm.mbind {m a, a} (ma, lam (x: m (a)): m (a) =<cloref1> x)
in
  res
end // end of [mmonad_join]

implement
mmonad_lift {m}{a1,r} (pfm, mcf, ma1) = let
  val x1 =
    pfm.mbind (mcf, lam (cf: cfun (a1,r)): m (r) =<cloref1> 
    pfm.mbind (ma1, lam (a1: a1): m (r) =<cloref1> let
      val x = cf (a1)
    in
      pfm.mretn x
    end))
in
  x1
end // end of [mmonad_lift]

implement
mmonad_ap {m}{a,b} (pfm, mcf, ma) =
  pfm.mbind (mcf, lam (cf) =>
  pfm.mbind (ma, lam (a) =>
  pfm.mretn (cf (a))))

(* ****** ****** *)

typedef ident (a:t@ype) = a

extern
val ident_monad: mmonad (ident)

implement
ident_monad = let
  val retn =
    lam {a:t@ype} (x: a): ident (a) =<cloref1> x
  val bind =
    lam {a,b:t@ype}
        (ma : ident (a), fmb : a -<cloref1> ident(b)): ident (b) =<cloref1> fmb(ma)
in $rec{
  mretn= retn,
  mbind= bind
} end // end of [ident_monad]

extern
val
ident_run : {a:t@ype} (ident (a)) -> a
implement
ident_run {a} (x) = x

(* ****** ****** *)

// this is akin to a constructive proof-term
// asserting that Option is a monad
extern
val option_monad: mmonad (Option)

implement
option_monad = let
  val retn =
    lam {a:t@ype} (x: a): Option (a) =<cloref1>
        Some (x)
  val bind =
    lam {a,b:t@ype}
        (ma : Option (a), fmb : a -<cloref1> Option(b)): Option (b) =<cloref1>
            case+ ma of None () => None () | Some a => fmb(a)
in $rec{
  mretn= retn,
  mbind= bind
} end // end of [option_monad]

// Option, aka Maybe, monad supplements
extern
fun
mopt_fail{a:t@ype} (): Option (a)
implement
mopt_fail {a} () = None ()
extern
fun
mopt_run {a:t@ype} (Option(a), INV(a)): a
implement
mopt_run {a} (mx, a) = case+ mx of None () => a | Some x => x


(* ****** ****** *)
// this monad is more realistic for C implementation

abstype monad (a:t@ype) = ptr
// a -> m a
extern
val
monad_return : {a:t@ype} cfun (INV(a), monad (a))
// m a -> (a -> m b) -> m b
extern
val
monad_bind : {a,b:t@ype} cfun2 (monad (INV(a)), cfun (a, monad (INV(b))), monad (b))

(* ****** ****** *)

// generic functions that only depend on monad API
extern
val
monad_join : {a:t@ype} cfun (monad (monad (a)), monad (a))
implement
monad_join {a} (ma) = monad_bind (ma, lam (a) => a)

extern
val
monad_lift : {a1,r:t@ype} cfun (cfun (a1, r), monad (a1), monad (r))
implement
monad_lift {a1,r} = lam (cf, ma1) => let
  val r = monad_bind (ma1, lam (a1) => monad_return (cf (a1)))
in
  r
end

extern
val
monad_ap : {a,b:t@ype} cfun (monad (cfun (a, b)), monad (a), monad (b))
implement
monad_ap {a,b} = lam (mcf, ma) => let
  val r = monad_bind (mcf, lam (cf) => let
  in
    monad_bind (ma, lam (a) => let
    in
      monad_return (cf (a))
    end)
  end)
in
  r
end

(* ****** ****** *)
//
assume monad (a) = Option (a)
//
implement
monad_return {a} (x) = Some (x)
implement
monad_bind {a,b} (ma, fmb) = case+ ma of
  | None () => None ()
  | Some a => fmb(a)

// Option, aka Maybe, monad supplements
extern
fun
opt_fail{a:t@ype} (): monad (a)
implement
opt_fail {a} () = None ()
extern
fun
opt_run {a:t@ype} (monad (a), INV(a)): a
implement
opt_run {a} (mx, a) = case+ mx of None () => a | Some x => x

(* ****** ****** *)
//
extern
fun
hello(): void = "mac#"
implement
hello() = let
//
  // dictionary-based approach
  val () = {
    val pfm = ident_monad
    val y = pfm.mbind (pfm.mretn {string} ((g0ofg1)"hi"), lam (x:string) =<cloref1> let
      val y = x + " world"
    in
      pfm.mretn (y)
    end) (* end of [val] *)
    val y = ident_run {string} (y)
    val () = print (y)
    val () = print_newline ()
  } (* end of [val] *)
  val () = {
    val pfm = option_monad
    val y = pfm.mbind (pfm.mretn ((g0ofg1)1), lam (x:int) =<cloref1> let
        val x1 = add_int0_int0 (x, (g0ofg1)1)
      in
        pfm.mretn{int} (x1)
      end) (* end of [val] *)
    val fz = pfm.mretn (lam (x:int):int =<cloref1> x+x * 3)
    val z = mmonad_ap {Option} (pfm, fz, y)
    val z = mopt_run (z, (g0ofg1)10)
    val () = print (z)
    val () = print_newline ()
  } (* end of [val] *)
//
  // "traditional" approach
  val () = {
      val y = monad_bind (monad_return ((g0ofg1)1), lam x => let
          val x1 = x + 1
        in
          monad_return (x1)
        end) (* end of [val] *)
      val fz = monad_return (lam (x:int):int =<cloref1> x+x * 3)
      val z = monad_ap (fz, y)
      val z = opt_run (z, (g0ofg1)10)
      val () = print (z)
      val () = print_newline ()
  }
//
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