module Probabilism

open FStar.Real

type prob = p:real{p >=. 0.0R}
type prob_post a = a -> GTot prob
type prob_pre = prob
type prob_wp a = prob_post a -> GTot prob_pre

// let prob_return (#a:eqtype) (x:a) (y:a) : nat = if (x=y) then 1 else 0


let xxx (a:Type): a = admit ()

let prob_return  (a:Type) (x:a) (p:prob_post a) : GTot prob_pre = p x

let prob_bind_wp (r1:range)
		 (a:Type) (b:Type)
                 (wp1:prob_wp a)
                 (wp2:(a -> GTot (prob_wp b)))
                 (p:prob_post b) : GTot prob_pre =
  wp1 (fun x -> wp2 x p)

assume val largest : (prob -> GTot Type0) -> GTot prob

assume val inf : (a:Type) -> (a -> GTot prob) -> GTot prob

assume val min : prob -> prob -> prob

assume val r_ITE : Type0 -> prob -> prob -> prob

let prob_if_then_else   (a:Type) (p:Type0)
                             (wp_then:prob_wp a) (wp_else:prob_wp a)
                             (post:prob_post a) : GTot (prob_pre) =
  r_ITE p (wp_then post) (wp_else post)

let prob_ite_wp (a:Type)
                (wp:prob_wp a)
                (post:prob_post a) : prob_pre =
admit()


unfold let prob_stronger   (a:Type) (wp1:prob_wp a)
                        (wp2:prob_wp a) : Type0 =
  forall p. wp1 p <=. wp2 p


unfold let prob_close_wp       (a:Type) (b:Type)
                             (wp:(b -> GTot (prob_wp a)))
                             (p:prob_post a) : prob_pre =

admit()

unfold let prob_assert_p       (a:Type) (p:Type0)
                             (wp:prob_wp a)
                             (q:prob_post a) : prob_pre =
admit()

unfold let prob_assume_p       (a:Type) (p:Type0)
                             (wp:prob_wp a)
                             (q:prob_post a) : prob_pre =
admit()

unfold let prob_null_wp        (a:Type)
                             (p:prob_post a) : prob_pre =
admit()

unfold let prob_trivial        (a:Type)
                             (wp:prob_wp a) =
True

new_effect {
  PROB : result:Type -> wp:prob_wp result -> Effect
  with return_wp    = prob_return 
     ; bind_wp      = prob_bind_wp 
     ; if_then_else = prob_if_then_else 
     ; ite_wp       = prob_ite_wp 
     ; stronger     = prob_stronger 
     ; close_wp     = prob_close_wp 
     ; assert_p     = prob_assert_p 
     ; assume_p     = prob_assume_p 
     ; null_wp      = prob_null_wp 
     ; trivial      = prob_trivial 
}

let prob_pre_0 : prob_pre = 0.0R

assume val ret : (a:Type) -> (x:a) -> PROB a (fun post -> post x)

type singleton_set (a:eqtype) = f: (a -> Type) { (exists x. f x) /\ (forall x y. f x /\ f y ==> x=y) }

assume val unique_extraction : (a:eqtype) -> (f:singleton_set a) -> x:a{f x}

effect ProbTot (a:Type) = PROB a (fun post -> inf a (fun x -> post x))

(*
let pure_return (a:Type) (x:a) (p:pure_post a) =
     forall (return_val:a). return_val==x ==> p return_val

lift_pure_prob (pure_return x) p 
= largest (fun r -> forall rv. rv==x ==> p rv >= r)
= largest (fun r -> p x >= r)
= p x
= prob_return x p
*)

let lift_pure_prob (a:Type) (wp:pure_wp a) (p:prob_post a) : GTot prob_pre = 
  largest (fun r -> wp (fun x -> p x >=. r))

sub_effect PURE ~> PROB = lift_pure_prob

assume val ret_hello : unit -> PROB string (fun post -> post "hello")

assume val lemma1: unit -> Lemma(forall post. inf string post <=. post "hello")

let a (x:real) : PROB string (fun post -> post "hello") = ret_hello ()

let a1 (x:real) : ProbTot string = ret_hello ()

let b (x:real) : PROB string (fun post -> 0.0R) = a x

let c (x:real) : PROB string (fun post -> post "hello") = "hello"
