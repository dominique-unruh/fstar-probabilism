module Test

open FStar.Tactics

let empty = _:unit{False}
let g : unit -> bool = fun x -> true
let h : unit -> bool = fun x -> false
let gh (x:empty) : Lemma(g x == h x) = ()

let unsound () : Lemma(False) =
  assert ((fun (x:empty) -> g x) == (fun (x:empty) -> h x)) by (l_to_r [`gh]); // by substituting
  assert (g == h);  // by eta-reduction
  assert (g () == h ())
