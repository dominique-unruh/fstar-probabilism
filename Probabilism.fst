module Probabilism

open FStar.Real
open FStar.List.Tot
  
unfold let pr = p:real{p >=. zero}
let prob_post (a:Type) = a -> Tot pr
unfold let prob_pre = pr
let prob_wp (a:Type) = prob_post a -> Tot prob_pre

assume type distribution (a:Type) : Type

assume val point_distribution (#a:Type) (x:a) : distribution a

assume val uniform_distribution (#a:Type) (x:list a{Cons? x}) : distribution a

let prob (a:Type) (w:prob_wp a): Tot Type0 =
  distribution a // TODO: require w to hold

let prob_wreturn a x : prob_wp a = fun(p:prob_post a) -> p x

let prob_return a (x:a) : prob a (prob_wreturn a x) = 
  point_distribution x

let prob_wbind a b (w1:prob_wp a) (w2:a -> prob_wp b) : prob_wp b = fun p -> w1 (fun x -> w2 x p)

let prob_bind a b (w1:prob_wp a) (w2:a -> prob_wp b)
      (f: prob a w1) (g: (x:a -> prob b (w2 x))) : prob b (prob_wbind a b w1 w2) =
   admit()   

let cast a (x:a) = x

// let blabla #a (w1 w2 : prob_wp a) : Type0 = (forall (p:prob_post a). (w2 p <=. w1 p))

let prob_stronger #a (w1 w2:prob_wp a) = forall x. w1 x <=. w2 x

let prob_subcomp a (#w1 #w2 : prob_wp a) (f:prob a w1) : 
                 Pure (prob a w2) (requires w2 `prob_stronger` w1) (ensures (fun _ -> True)) =
  f

//let stronger_refl #a (w:prob_wp a): Lemma(w `prob_stronger` w) = ()

let ite_prob a (#w1 #w2 : prob_wp a) (f: prob a w1) (g: prob a w2) (b: bool) : Type =
  prob a (if b then w1 else w2)

// [@@allow_informative_binders] // Can we get rid of this and still have reifiable?
total
//reifiable
reflectable
layered_effect { PROB : (a:Type) -> (wp:prob_wp a) -> Effect with 
  repr = prob;
  return = prob_return; 
  bind = prob_bind;
  subcomp = prob_subcomp;
  if_then_else = ite_prob
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

let hint a : squash(forall (y x:a). (forall post. post y ==> post x) ==> (x == y)) = admit()

let hint_string () = hint string

let average (l:list pr{Cons? l}) : pr =
  assume False;
  (fold_left (fun pr x -> pr +. x) zero l) /. of_int (length l)

let pick #a (l:list a{Cons? l}) : PROB a (fun post -> average (map post l)) =
  PROB?.reflect (uniform_distribution l)

let coin () : PROB bool (fun post -> (post true +. post false) /. two) =
  PROB?.reflect (uniform_distribution [true;false])

(**** TESTS *****)

let test1 () : PROB bool (fun p -> (p true +. p false) /. two) = coin ()

let test2 () : PROB bool (fun p -> zero) = coin ()

let test3 x : PROB string (fun p -> p x) = x

let test4 () : PROB string (fun post -> post "hello") = test3 "hello"

let f (b:bool) : nat = if b then 0 else 1

let return (#a) (x:a) : PROB a (fun p -> p x) = 
  PROB?.reflect (prob_return a x)

let test5 () : PROB nat (fun p -> (p 0 +. p 1) /. two) =
  let c : bool = coin() in
  return (f c)

// FAILS
(* let test6 () : PROB nat (fun p -> (p 0 +. p 1) /. two) =
  let c : bool = coin() in
  return (if c then 0 else 1) *)

// FAILS
(* let test7 () : PROB nat (fun p -> (p 0 +. p 1) /. two) =
  let c : bool = coin() in
  f c *)

let prob_unit : prob_wp unit = fun p -> p ()

// FAILS
(* let test7 () : PROB nat (fun p -> (p 0 +. p 1) /. two) =
  let c : bool = coin() in
  (if c then return 0 else return 1) *)


// let reified = reify (test2 ())

// let coin_vs_pick () : Lemma(coin () == pick [true;false]) = ()

