// hello from 2012!
//
// compile with atscc, compiler for ATS, an ML dialect
// see <www.ats-lang.org>

staload _ = "prelude/DATS/list.dats"
staload _ = "prelude/DATS/string.dats"

// the type of dynamic terms
// NOTE: using an abstract type here would be true
// to the spirit of dynamically typed languages
datatype DT =
  | DTint of int | DTstr of string | DTlst of List DT
  | DTfun of DT -<1> DT

// printing
fun put (x: DT): void = case+ x of
  | DTint x => print x
  | DTstr x => print x
  | DTlst xs => let
      fun loop (xs: List DT): void = case+ xs of
        | list_cons (x, xs) => begin
	    put x;
	    if list_is_cons xs then print ", ";
	    loop xs
          end // end of [begin]
        | list_nil () => () // nothing
    in
      print "["; loop xs; print "]"
    end // end of [let]
  | DTfun f => print "<fun>"

fun len (x: DT): int = case+ x of
  | DTlst xs => list_length<DT> (xs)
  | DTstr s => int_of_size (string_length s)
  | _ => begin
      prerr "[len]: type error\n";
      exit {int} (1)
    end

fun hd (x: DT): DT = case+ x of
  | DTlst xs => begin
      case+ xs of
      | list_cons (x, xss) => x
      | list_nil () => begin
      	  prerr ("[hd]: list is empty\n");
	  exit {DT} (1)
	end
    end
  | _ => begin
      prerr "[hd]: type error\n";
      exit {DT} (1)
    end

fun sort (x: &DT): void = () // TODO: implement; only valid on lists but not strings

fun test (l: &DT): void = begin
  if len l > 0 then begin
    l := hd l;
    put l
  end;
  if len l <= 0 then begin
    sort l
  end
end

implement main () = let
  // we may as well introduce more operations on [DT]
  // to ease constructing "dynamically-typed" terms
  var l = DTlst (list_cons (DTstr "hello", list_cons (DTint 5, list_nil ())))
in
  test l
end // end of [main]