module Probabilism

open FStar.Real

type pr = p:real{p >=. 0.0R}
type prob_post a = a -> GTot pr
type prob_pre = pr
type prob_wp a = prob_post a -> GTot prob_pre

assume val distribution : (a:Type) -> Type

assume val point_distribution : (a:Type) -> a -> distribution a

type prob (a:Type) (w:prob_wp a): Type =
  distribution a // TODO: require w to hold

let prob_wreturn a x : prob_wp a = fun(p:prob_post a) -> p x

let prob_return a (x:a) : prob a (prob_wreturn a x) = 
  point_distribution a x

let prob_wbind a b (w1:prob_wp a) (w2:a -> prob_wp b) : prob_wp b = fun p -> w1 (fun x -> w2 x p)

let prob_bind a b (w1:prob_wp a) (w2:a -> prob_wp b)
      (f: prob a w1) (g: (x:a -> prob b (w2 x))) : prob b (prob_wbind a b w1 w2) = 
  admit()

reifiable reflectable new_effect { PROB : (a:Type) -> Effect with 
  repr = prob;
  return = prob_return; 
  bind = prob_bind
(*  if_then_else = admit();
  ite_wp = admit();
  stronger = admit();
  close_wp = admit();
  assert_p = admit();
  assume_p = admit();
  null_wp = admit();
  trivial = admit() *)
  }
  
