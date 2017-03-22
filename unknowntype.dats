#include
"share/atspre_staload.hats"

absprop t0ype_tag (i:int, a:t@ype)
extern
praxi t0ype_tag_int : () -> t0ype_tag (0, int)
extern
praxi t0ype_tag_float : () -> t0ype_tag (1, float)
extern
praxi t0ype_tag_int_float : () -> t0ype_tag (2, @(int,float))
extern
praxi t0ype_tag_isfun : {i:int}{a,b:t@ype} (t0ype_tag (i, a), t0ype_tag (i, b)) -> EQTYPE (a, b)

extern
fun{a:t@ype}
printme {i:int} (t0ype_tag (i, a) | tag: int (i), x: &INV(a)): void
implement{a}
printme {i} (pf | tag, x) =
  if tag = 0 then let
      prval pf1 = t0ype_tag_int ()
      prval EQTYPE () = t0ype_tag_isfun {i} (pf1, pf)
      val () = print!("int: ")
      val () = print_int (x)
      val () = print_newline ()
    in
    end
  else if tag = 1 then let
      prval pf1 = t0ype_tag_float ()
      prval EQTYPE () = t0ype_tag_isfun {i} (pf1, pf)
      val () = print!("float: ")
      val () = print_float (x)
      val () = print_newline ()
    in
    end
  else if tag = 2 then let
      prval pf1 = t0ype_tag_int_float ()
      prval EQTYPE () = t0ype_tag_isfun {i} (pf1, pf)
      val px = addr@(x)
      prval [l:addr] EQADDR () = eqaddr_make_ptr (px)
      prval pf_at = view@(x)
      prval pf_at = pf_at : @(int,float) @ l
      val () = println!("int/float: ", !px.0, ", ", !px.1)
      prval () = view@(x) := pf_at
    in
    end
  else println!("unknown tag: ", tag)

implement
main0 () = {
  var x = (g0ofg1)1
  var y = 2.0f
  var xy = @(x, y)
  val () = printme<int> (t0ype_tag_int () | 0, x)
  val () = printme<float> (t0ype_tag_float () | 1, y)
  val () = printme< @(int,float) > (t0ype_tag_int_float () | 2, xy)
}
