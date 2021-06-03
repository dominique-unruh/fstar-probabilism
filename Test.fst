module Test


open FStar.Tactics

let e_wp (a:Type) : Type = nat -> Type0
let e_repr (a:Type) (w:e_wp a) : Type = _:a{w 5}

assume val ew_return (a:Type) (x:a) : e_wp a
assume val e_return (a:Type) (x:a) : e_repr a (ew_return a x)

assume val ew_bind (a b:Type) (w1:e_wp a) (w2:a->e_wp b) : e_wp b
assume val e_bind (a b:Type) (w1:e_wp a) (w2:a->e_wp b)       (f: e_repr a w1) (g: (x:a -> e_repr b (w2 x))) : e_repr b (ew_bind a b w1 w2)

total
reflectable
reifiable
layered_effect { E : (a:Type) -> (wp:e_wp a) -> Effect with 
  repr = e_repr;
  return = e_return; 
  bind = e_bind
//  subcomp = prob_subcomp;
//  if_then_else = ite_prob
  }


let e1 #a : e_wp a = (fun _ -> True) 
let e2 #a : e_wp a = (fun n -> n==5) 

let ew_lift a (wp:pure_wp a) = e1 #a

let e_lift a (wp:pure_wp a) (f: eqtype_as_type unit -> PURE a wp) : 
   e_repr a (ew_lift a wp) =
   admit()
   

sub_effect PURE ~> E = e_lift


let also_type (#a #b #b': Type) (#wp1:a -> e_wp b) (p:(x:a) -> E b (wp1 x)) (wp2:a -> e_wp b') = unit -> q:(x:a -> E b' (wp2 x)) {forall(x:a). reify (p x) === reify (q x)}
 
let test () : E unit e1 = E?.reflect ()

let test_also : also_type test (fun () -> e2 #unit) = 
  fun () ->
  let p' = reify (test ()) in
  let q : unit -> E unit e2 = (fun x -> E?.reflect p') in
  assert (reify (test ()) === reify (q ())) by ();
  q

