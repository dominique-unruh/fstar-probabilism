(*

This file sketches the modeling and use of the PROB effect based on
the wp-approach.

It only contains the basic definitions at this point.

*)

module ProbabilismHoare

open FStar.Real
open FStar.List.Tot
open FStar.Tactics
open FStar.FunctionalExtensionality

(* let tmp () : Lemma(exists (f:prop -> bool). f True = true /\ f False = false) =
assert(~ (True == False));
  assert_by_tactic(exists (f:bool -> bool). f true = true /\ f false = false)
(fun _ ->
smt();
dump "tmp";
admit_all());
admit() *)

let pr = r:real{r >=. zero}
let prob_pre = pr
let prob_post (a:Type) = a -> Tot pr
let prob_wp (a:Type) = prob_pre ^-> prob_post a ^-> prop

assume type distribution (a:Type) : Type

assume val point_distribution (#a:Type) (x:a) : distribution a

assume val uniform_distribution (#a:Type) (x:list a{Cons? x}) : distribution a

let prob_wp_eqI #a (wp1 wp2: prob_wp a) :
    Lemma (requires (forall pre post. wp1 pre post == wp2 pre post))
          (ensures (wp1 == wp2)) = 
    assert (forall pre. feq (wp1 pre) (wp2 pre));
    assert (feq wp1 wp2);
    assert (wp1 == wp2)

let prob a (w:prob_wp a): Tot Type0 =
  distribution a // TODO: require w to hold

let b2p (b: bool) : prop = b == true
let t2p (t: Type0) : prop = t

let prob_wreturn #a x : prob_wp a = 
    on _ (fun (pre:prob_pre) -> on _ (fun (post:prob_post a) -> b2p (pre <=. post x)))

let prob_return a (x:a) : prob a (prob_wreturn x) = 
  point_distribution x

let prob_wbind #a #b (w1:prob_wp a) (w2:a -> prob_wp b) : prob_wp b = 
    on _ (fun (pre:prob_pre) -> on _ (fun (post:prob_post b) ->
      exists (mid:prob_post a). w1 pre mid /\ (forall (x:a). w2 x (mid x) post)))

let prob_bind a b (w1:prob_wp a) (w2:a -> prob_wp b)
      (f: prob a w1) (g: (x:a -> prob b (w2 x))) : prob b (prob_wbind w1 w2) =
   admit()   

let stronger #a (w1 w2:prob_wp a) = forall post pre. w2 post pre ==> w1 post pre

let prob_wp_stronger_eq #a (w1 w2:prob_wp a) :
    Lemma (requires w1 `stronger` w2 /\ w2 `stronger` w1)
    	  (ensures w1 == w2) = 
    assert (w1 == w2) by (
apply_lemma (`prob_wp_eqI);
let pre = forall_intro_as "pre" in
let post = forall_intro_as "post" in
let _ = pose_lemma (`FStar.PropositionalExtensionality.axiom) in
dump "";
admit_all()
)

let prob_subcomp a (w1 w2 : prob_wp a) (f:prob a w1) : 
                 Pure (prob a w2) (requires w1 `prob_stronger` w2) (ensures (fun _ -> True)) =
  f

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

// assume val smallest : #a:Type -> (a->Type) -> (a->pr) -> pr

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

let lift_pure_prob_wp #a (wp:pure_wp a) : prob_wp a =
    fun pre post -> wp (fun x -> pre <=. post x)

let lift_pure_prob a (wp:pure_wp a) (f: eqtype_as_type unit -> PURE a wp) : 
   prob a (lift_pure_prob_wp wp) =
   assume False; // TODO
   point_distribution (f ())
   
sub_effect PURE ~> PROB = lift_pure_prob

// let hint a : squash(forall (y x:a). (forall post. post y ==> post x) ==> (x == y)) = admit()

// let hint_string () = hint string

(* let average (l:list pr{Cons? l}) : pr =
  assume False;
  (fold_left (fun pr x -> pr +. x) zero l) /. of_int (length l)

let pick #a (l:list a{Cons? l}) : PROB a (fun post -> average (map post l)) =
  PROB?.reflect (uniform_distribution l) *)

let simple_wp #a (wp: prob_post a -> pr) : prob_wp a = fun pre post -> pre <=. wp post

let coin () : PROB bool (simple_wp (fun post -> (post true +. post false) /. two)) =
  PROB?.reflect (uniform_distribution [true;false])

(**** TESTS *****)

let test1 () : PROB bool (simple_wp (fun post -> (post true +. post false) /. two)) = coin ()

let test2 () : PROB bool (fun pre post -> False) = coin ()

(* let return (#a) (x:a) : PROB a (prob_wreturn x) = 
  PROB?.reflect (prob_return a x) *)

(* let map_return (#a) (#b) (f:a->b) (x:a) : PROB b (prob_wreturn b (f x)) = 
  PROB?.reflect (prob_return b (f x)) *)

// let test2' () : PROB bool (fun p -> zero) = let c = coin () in c

let test3 x : PROB string (prob_wreturn x) = x

let test4 () : PROB string (prob_wreturn "hello") = test3 "hello"

let f (b:bool) : nat = if b then 0 else 1

let goal = (ProbabilismHoare.prob_stronger (ProbabilismHoare.prob_wbind #Prims.bool
             #Prims.nat
             (fun pre post -> pre <=. (post true +. post false) /. FStar.Real.two)
             (fun c -> ProbabilismHoare.prob_wreturn #Prims.nat (ProbabilismHoare.f c)))
         (fun pre post -> pre <=. (post 0 +. post 1) /. FStar.Real.two))

// let void #a (x:a) = ()

(*let xx = assert_by_tactic (exists n. n=1) (fun () ->
    witness (`2);
    dump "Test";
    admit_all()
)*)

irreducible
let bind_return #a #b (wp1:prob_wp a) (f:a->b) : Lemma(prob_wbind wp1 (fun x -> prob_wreturn (f x)) 
                                  == (fun pre post -> wp1 pre (fun x -> post (f x)))) =
  admit()				     

irreducible
let return_bind #a #b (x:a) (wp2:a -> prob_wp b) : Lemma(prob_wbind (prob_wreturn x) wp2 == wp2 x) =
  admit()

irreducible
let bind_simple_return #a #b wp1 f : Lemma(prob_wbind (simple_wp wp1) (fun x -> prob_wreturn (f x)) 
                                  == simple_wp (fun post -> wp1 (fun x -> post (f x)))) =

    assert (prob_wbind (simple_wp wp1) (fun x -> prob_wreturn (f x)) 
        == simple_wp (fun post -> wp1 (fun x -> post (f x))))
	by (
	dump "x";
	apply_lemma(`xxx);
	admit_all()
);

()

(*  
  bind_return (simple_wp wp1) f;
  assert (forall pre post. prob_wbind (simple_wp wp1) (fun x -> prob_wreturn (f x)) pre post
       == simple_wp (fun post -> wp1 (fun x -> post (f x))) pre post);
  admit();
  ()				     

(* let simple_wp #a (wp: prob_post a -> pr) : prob_wp a = fun pre post -> pre <=. wp post
 *)

let test5 () : PROB nat (simple_wp (fun post -> (post 0 +. post 1) /. two)) by (
unfold_def (`pure_null_wp);
norm[];
  dump "vc"
) =
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

