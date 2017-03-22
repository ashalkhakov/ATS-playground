    typedef lightbulb (b: bool) = @{is_turned_on= bool b, light_intensity= intBtw (1, 10)}

    fn lightbulb_make {b:bool} (state: bool b, intensity: intBtw (1, 10)) :<> lightbulb b =
      @{is_turned_on= state, light_intensity= intensity}

    // The [&T1 >> T2] notation means that function expects to be given
    // a term of type T1, and then on exit, the type of the term will
    // change to T2.
    // In our case, the function expects a lightbulb either turned on or off,
    // but on exit, the lightbulb will be turned off. (These conditions
    // are typically referred to as pre- and postconditions of a function.)
    fn lightbulb_turn_on {b:bool} (x: &lightbulb b >> lightbulb true) :<> void =
      x.is_turned_on := true

    fn lightbulb_change_intensity {b:bool} (x: &lightbulb b, y: intBtw (1, 10)) :<> void =
      x.light_intensity := y

    implement main () = let
      var bulb = lightbulb_make (false, 5)
      val () = lightbulb_turn_on (bulb)
      val () = lightbulb_change_intensity (bulb, 3)
    in
      printf ("intensity is now: %d\n", @(bulb.light_intensity))
    end

