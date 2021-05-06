// -*- mode: fstar; -*-

module Probabilism

open FStar.Real
open FStar.List.Tot
open FStar.Tactics

let pr = r:real{r >=. zero}
let prob_pre = pr
let prob_post (a:Type) = a -> Tot pr
let prob_wp (a:Type) = prob_pre -> prob_post a -> Type0

assume type distribution (a:Type) : Type

assume val point_distribution (#a:Type) (x:a) : distribution a

assume val uniform_distribution (#a:Type) (x:list a{Cons? x}) : distribution a

let prob (a:Type) (w:prob_wp a): Tot Type0 =
  distribution a // TODO: require w to hold

let prob_wreturn a x : prob_wp a = fun (pre:prob_pre) (post:prob_post a) -> pre <=. post x

let prob_return a (x:a) : prob a (prob_wreturn a x) = 
  point_distribution x

let prob_wbind a b (w1:prob_wp a) (w2:a -> prob_wp b) : prob_wp b = 
    fun (pre:prob_pre) (post:prob_post b) ->
    exists (mid:prob_post a). w1 pre mid /\ (forall (x:a). w2 x (mid x) post)

let prob_bind a b (w1:prob_wp a) (w2:a -> prob_wp b)
      (f: prob a w1) (g: (x:a -> prob b (w2 x))) : prob b (prob_wbind a b w1 w2) =
   admit()   

let cast a (x:a) = x

// let blabla #a (w1 w2 : prob_wp a) : Type0 = (forall (p:prob_post a). (w2 p <=. w1 p))

let prob_stronger #a (w1 w2:prob_wp a) = forall post pre. w2 post pre ==> w1 post pre

let prob_subcomp a (#w1 #w2 : prob_wp a) (f:prob a w1) : 
                 Pure (prob a w2) (requires w1 `prob_stronger` w2) (ensures (fun _ -> True)) =
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

assume val smallest : #a:Type -> (a->Type) -> (a->pr) -> pr

// effect PTotal a (pre:prop) (post:a->prop) = PROB a (fun p -> smallest (fun x -> pre ==> post x) p)
// effect PPartial a (pre:Type0) (post:a->Type0) = PROB a (fun p -> ? smallest (fun x -> pre ==> post x) p)


(*
I think the problem with the definition is the following:

In a call such as "f x" where x:t is pure and f:t->PROB u, this
desugars roughly to "bind_prob (lift_pure_prob x) f" lift_pure_prob x
has an implicit #pwp that needs to be instantiated, but bind_prob does
not put any constraint on the wp returned by lift_pure_prob, so there
is no information how to instantiate #pwp. Hence "f x" fails (in many
cases).

Ideas:

* Is there some way how to guide the insertion of implicits?

* Can we define a function "list_pure_prob_wp : pure_wp a -> prob_wp
  a" so that we do not need #pwp. Problem: this needs a function
  "largest (real -> Type)" that is probably not implementable and
  whose axiomatized existence might be unsound (allows to solve the
  halting problem or equality on functions). largest could be
  constrained to require that the input is a Dedekind cut, but it is
  still not obvious that largest would be sound then. (Also, this
  approach might not even be possible for quantum WPs because
  Hermitian operators form an antilattice.)

* Can we add type hints in a PROB function to indicate the wp's? 

* Can we tell F* to avoid using the lifting in cases where it cancels
  out anyway? (E.g., "bind_prob (lift_pure_prob x) f" could just be "f
  x".

* We can define prob_wp as a union type "Prob_WP of (prob_post ->
  prob_pre) | Pure_WP of pure_wp". Then translating from PURE to PROB
  is trivial. All other monadic transformations need to be adapted to
  deal with the case distinction. (In particular subcomp must handle
  comparison between PURE and PROB (in one direction only).)

* Model reals as dedekind cuts

* Model prob_wp a := prob_post a -> Type0. Intuition: (prob_wp a p)
  holds iff expectation of p is >= 1.

* Model prob_wp a := relation between pre/post-condition

*)

let lift_pure_prob_wp (a:Type) (wp:pure_wp a) : prob_wp a =
    fun pre post -> wp (fun x -> pre <=. post x)

let lift_pure_prob (a:Type) (wp:pure_wp a) (f: eqtype_as_type unit -> PURE a wp) : 
   prob a (lift_pure_prob_wp a wp) =
   assume False; // TODO
   point_distribution (f ())
   
sub_effect PURE ~> PROB = lift_pure_prob

let hint a : squash(forall (y x:a). (forall post. post y ==> post x) ==> (x == y)) = admit()

let hint_string () = hint string

(* let average (l:list pr{Cons? l}) : pr =
  assume False;
  (fold_left (fun pr x -> pr +. x) zero l) /. of_int (length l)

let pick #a (l:list a{Cons? l}) : PROB a (fun post -> average (map post l)) =
  PROB?.reflect (uniform_distribution l) *)

let coin () : PROB bool (fun pre post -> pre <=. (post true +. post false) /. two) =
  PROB?.reflect (uniform_distribution [true;false])

(**** TESTS *****)

let test1 () : PROB bool (fun pre post -> pre <=. (post true +. post false) /. two) = coin ()

let test2 () : PROB bool (fun pre post -> False) = coin ()

let return (#a) (x:a) : PROB a (prob_wreturn a x) = 
  PROB?.reflect (prob_return a x)

let map_return (#a) (#b) (f:a->b) (x:a) : PROB b (prob_wreturn b (f x)) = 
  PROB?.reflect (prob_return b (f x))

// let test2' () : PROB bool (fun p -> zero) = let c = coin () in c

let test3 x : PROB string (prob_wreturn _ x) = x

let test4 () : PROB string (prob_wreturn _ "hello") = test3 "hello"

let f (b:bool) : nat = if b then 0 else 1

let goal = (Probabilism.prob_stronger (Probabilism.prob_wbind Prims.bool
             Prims.nat
             (fun pre post -> pre <=. (post true +. post false) /. FStar.Real.two)
             (fun c -> Probabilism.prob_wreturn Prims.nat (Probabilism.f c)))
         (fun pre post -> pre <=. (post 0 +. post 1) /. FStar.Real.two))

let void #a (x:a) = ()

(*let xx = assert_by_tactic (exists n. n=1) (fun () ->
    witness (`2);
    dump "Test";
    admit_all()
)*)

let admit_nt a (n:string) : a = admit ()

let tmp () : Lemma(forall (_: Prims.unit). (forall (pre: Probabilism.prob_pre) (post: Probabilism.prob_post Prims.nat).
       (*could not prove post-condition*) FStar.Real.two <> 0.0R) /\
   Prims.auto_squash (Probabilism.prob_stronger (Probabilism.prob_wbind Prims.bool
             Prims.nat
             (fun pre post -> pre <=. (post true +. post false) /. FStar.Real.two)
             (fun c -> Probabilism.prob_wreturn Prims.nat (Probabilism.f c)))
         (fun pre post -> pre <=. (post 0 +. post 1) /. FStar.Real.two))) = 
    assert_by_tactic
    ((forall (pre: Probabilism.prob_pre) (post: Probabilism.prob_post Prims.nat).
       (*could not prove post-condition*) FStar.Real.two <> 0.0R) /\
   Prims.auto_squash (Probabilism.prob_stronger (Probabilism.prob_wbind Prims.bool
             Prims.nat
             (fun pre post -> pre <=. (post true +. post false) /. FStar.Real.two)
             (fun c -> Probabilism.prob_wreturn Prims.nat (Probabilism.f c)))
         (fun pre post -> pre <=. (post 0 +. post 1) /. FStar.Real.two)))
     (fun () -> 
     split();
     smt();
     squash_intro();
     let post = forall_intro_as("post") in
     let pre = forall_intro_as("pre") in
     let _ = implies_intro() in
     witness (`(fun x -> (`#pre) (f x)));
     dump "x")



let test5 () : PROB nat (fun pre post -> pre <=. (post 0 +. post 1) /. two) =
  let c : bool = coin() in
  f c

(*

// FAILS
(* let test6 () : PROB nat (fun p -> (p 0 +. p 1) /. two) =
  let c : bool = coin() in
  map_return (fun c -> if c then 0 else 1) c *)

// FAILS
(* let test7 () : PROB nat (fun p -> (p 0 +. p 1) /. two) =
  let c : bool = coin() in
  f c *)

let prob_unit : prob_wp unit = fun p -> p ()

// FAILS
(* let test7 () : PROB nat (fun p -> (p 0 +. p 1) /. two) =
  let c : bool = coin() in
  (if c then return 0 else return 1) *)

let test8 () : PROB bool (fun post -> (post true +. post false) /. two) =
  (if coin () then coin() else coin())


let test7 () : PROB nat (fun p -> (p 0 +. p 1) /. two) =
  let c : bool = coin() in
  (if true then return 0 else return 1)

// let reified = reify (test2 ())

// let coin_vs_pick () : Lemma(coin () == pick [true;false]) = ()

