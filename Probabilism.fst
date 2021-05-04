module Probabilism

open FStar.Real

let pr = p:real{p >=. 0.0R}
let prob_post (a:Type) = a -> Tot pr
let prob_pre = pr
let prob_wp (a:Type) = prob_post a -> Tot prob_pre

assume type distribution (a:Type) : Type

assume val point_distribution (#a:Type) (x:a) : distribution a

let prob (a:Type) (w:prob_wp a): Tot Type0 =
  distribution a // TODO: require w to hold

let prob_wreturn a x : prob_wp a = fun(p:prob_post a) -> p x

let prob_return a (x:a) : prob a (prob_wreturn a x) = 
  point_distribution x

let prob_wbind a b (w1:prob_wp a) (w2:a -> prob_wp b) : prob_wp b = fun p -> w1 (fun x -> w2 x p)

let prob_bind a b (w1:prob_wp a) (w2:a -> prob_wp b)
      (f: prob a w1) (g: (x:a -> prob b (w2 x))) : prob b (prob_wbind a b w1 w2) =
   admit()   

reflectable
layered_effect { PROB : (a:Type) -> (wp:prob_wp a) -> Effect with 
  repr = prob;
  return = prob_return; 
  bind = prob_bind
  }

unfold
let compatible (#a) (wp:pure_wp a) (pwp:prob_wp a) = 
    forall ppost x.
       (forall post. wp post ==> post x) ==> pwp ppost <=. ppost x

let lift_pure_prob (a:Type) (#pwp:prob_wp a) (wp:pure_wp a) (f: eqtype_as_type unit -> PURE a wp) : 
   Pure (prob a pwp) (requires compatible wp pwp) (fun x -> ensures True) =
//   FStar.Monotonic.Pure.wp_monotonic_pure ();
   assume False;
   point_distribution (f ())
   
sub_effect PURE ~> PROB = lift_pure_prob

unfold
let goal = (Probabilism.compatible (fun p ->
             forall (return_val: Prims.string). return_val == "hello" ==> p return_val)
         (fun p -> p "hello"))

let hint a : squash(forall (y x:a). (forall post. post y ==> post x) ==> (x == y)) = admit()

let hint_string () = hint string

let test3 x : PROB string (fun p -> p x) = x

let test2 () : PROB string (fun post -> post "hello") = test3 "hello"

// let reified = reify (test2 ())
