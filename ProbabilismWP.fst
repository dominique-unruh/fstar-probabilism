module ProbabilismWP

(* Approach with post -> real WP and with supremum axiom *)

open FStar.Real
open FStar.Tactics
open FStar.Tactics.Builtins
open FStar.IndefiniteDescription
open FStar.FunctionalExtensionality

let pr = r:real{r >=. zero}
let prob_post (a:Type) = a -> Tot pr
// TODO: add monotonicity
let prob_wp (a:Type) = prob_post a ^-> pr

assume type distribution (a:Type) : Type

assume val point_distribution (#a:Type) (x:a) : distribution a

assume val uniform_distribution (#a:Type) (x:list a{Cons? x}) : distribution a

let prob_wp_eqI #a (wp1 wp2: prob_wp a) :
    Lemma (requires (forall post. wp1 post = wp2 post))
          (ensures (wp1 == wp2)) =
    assert (feq wp1 wp2);
    assert (wp1 == wp2)

let prob a (w:prob_wp a): Tot Type0 =
  distribution a // TODO: require w to hold

let prob_wreturn #a x : prob_wp a =
  on _ (fun post -> post x)

let prob_return a (x:a) : prob a (prob_wreturn x) = 
  point_distribution x

let prob_wbind #a #b (w1:prob_wp a) (w2:a -> prob_wp b) : prob_wp b = 
  on _ (fun post -> w1 (fun x -> w2 x post))

let prob_wbind_beta #a #b (w1:prob_wp a) (w2:a -> prob_wp b) (post:prob_post b) :
  Lemma (prob_wbind w1 w2 post == w1 (fun x -> w2 x post)) = ()

let prob_bind a b (w1:prob_wp a) (w2:a -> prob_wp b)
      (f: prob a w1) (g: (x:a -> prob b (w2 x))) : prob b (prob_wbind w1 w2) =
   admit()   

// w1 is a more restrictive wp than w2
let stronger #a (w1 w2:prob_wp a) = forall post. w1 post >=. w2 post

let strongerI #a (w1 w2:prob_wp a) :
  Lemma (requires forall post. w1 post >=. w2 post)
        (ensures w1 `stronger` w2) = ()

let prob_wp_stronger_eq #a (w1 w2:prob_wp a) :
    Lemma (requires w1 `stronger` w2 /\ w2 `stronger` w1)
    	  (ensures w1 == w2) = 
    assert (w1 == w2) by (apply_lemma (`prob_wp_eqI))

let prob_subcomp a (w1 w2 : prob_wp a) (f:prob a w1) : 
                 Pure (prob a w2) (requires w1 `stronger` w2) (ensures (fun _ -> True)) =
  f

let ite_prob a (#w1 #w2 : prob_wp a) (f: prob a w1) (g: prob a w2) (b: bool) : Type =
  prob a (if b then w1 else w2)

total
reflectable
layered_effect { PROB : (a:Type) -> (wp:prob_wp a) -> Effect with 
  repr = prob;
  return = prob_return; 
  bind = prob_bind;
  subcomp = prob_subcomp;
  if_then_else = ite_prob
  }

assume val real_numbers_complete: unit -> Lemma(
  forall (p: real->bool) low high.
  p low ==> not (p high) ==> (forall x y. x >=. y ==> p x ==> p y) ==>
  (exists sup. (forall x. x <. sup ==> p x) /\ (forall x. x >. sup ==> not (p x))))

// TODO: add requires, ensures, define
assume val largest (p: pr -> Type0) : pr

let lift_pure_prob_wp #a (wp:pure_wp a) : prob_wp a =
    on _ (fun (post:prob_post a) -> largest (fun (p:pr) -> wp (fun x -> p <=. post x)))

let lift_pure_prob a (wp:pure_wp a) (f: eqtype_as_type unit -> PURE a wp) : 
   prob a (lift_pure_prob_wp wp) =
   assume False; // TODO
   point_distribution (f ())

sub_effect PURE ~> PROB = lift_pure_prob

effect Prob a (wp: prob_post a -> pr) = PROB a (on _ wp)
effect ProbAny (a:Type) = Prob a (fun post -> 0.0R)

let coin () : Prob bool (fun (post) -> (post true +. post false) /. two) =
  PROB?.reflect (uniform_distribution [true;false])

let test1 () : Prob bool (fun post -> (post true +. post false) /. two) = coin ()

let test2 () : ProbAny bool = coin ()

let test3 x : Prob string (prob_wreturn x) 
by (admit_all()) = assume False; x

let test4 () : PROB string (prob_wreturn "hello") = test3 "hello"

let f (b:bool) : nat = if b then 0 else 1

irreducible
let bind_return #a #b (wp1:prob_wp a) (f:a->b) : Lemma(prob_wbind wp1 (fun x -> prob_wreturn (f x))
                                  == on _ (fun(post:prob_post b) -> wp1 (fun x -> post (f x))))
  [SMTPat (prob_wbind wp1 (fun x -> prob_wreturn (f x)))]                                 
        =
  admit()				     

irreducible
let return_bind #a #b (x:a) (wp2:a -> prob_wp b) : Lemma(prob_wbind (prob_wreturn x) wp2 == wp2 x) 
  [SMTPat (prob_wbind (prob_wreturn x) wp2)]
  =
  admit()

let test5 () : Prob nat (fun post -> (post 0 +. post 1) /. two) =
  let c : bool = coin() in
  f c

let prob_wbind_on #a #b (wp1:prob_wp a) (wp2:a -> prob_wp b) : 
  Lemma(prob_wbind (on (prob_post a) #pr wp1) wp2 == prob_wbind wp1 wp2)
  [SMTPat (prob_wbind (on _ wp1) wp2)]
  = ()

(*
open FStar.Tactics.Simplifier

let equals_cong #t a b a' b' : Lemma
  (requires a == a' /\ b == b')
  (ensures (a == b) <==> (a' == b')) = ()

let conversion (relation:term) = term -> Tac (term * (unit -> Tac unit))

let dump_conversion (#relation:term) (msg:string) (c:conversion relation) : conversion relation = (fun t ->
  print (msg ^ " " ^ term_to_string t); 
  c t)

let equals = (`(==))

val id_conversion : conversion equals
let id_conversion t =
  (t, (fun () -> fail "id_conversion"))

let iff = (`(<==>))

val iff_id_conversion : conversion iff
let iff_id_conversion t =
  (t, (fun () -> fail "iff_id_conversion"))

let cut_conversion #relation (c:conversion relation) (t:term) : Tac binder =
  let (t', tac) = c t in
  let thm = (`(`#relation) (`#t) (`#t')) in
  

let xxx (a:nat) : nat by (
//  let (res, tac) = (dump_conversion "test" iff_id_conversion) (`(forall a. a)) in
  let h = cut_conversion iff_id_conversion (`(forall a. a)) in
  dump ""
) = a+a
*)

(* assert (prob_wbind (on_domain (prob_post bool)
              (fun (post) -> (post true +. post false) /. two))
          (fun (x) -> prob_wreturn 0)
          ==
          prob_wbind (on_domain (prob_post bool)
              (fun (post:prob_post bool) -> (post true +. post false) /. two))
          (fun (x:bool) -> prob_wreturn 0)
          )

*)


(* let x =
assert (forall a b (x y:a). a `subtype_of` b ==> eq2 #a x y ==> eq2 #b x y) *)

let test6 () : Prob nat (fun p -> p 0)
=
  let c : bool = coin() in 0

let on_beta #a #b (f:_->_) x : Lemma(on a #b f x == f x) = ()

(*let wrong #a (w1 w2: prob_wp a) : Lemma(w1 `stronger` w2) 
[SMTPat (w1 `stronger` w2) ]
= admit() *)

let bool_simp1 () : Lemma((true = true) == true) = ()
let bool_simp2 () : Lemma((false = true) == false) = ()
let bool_simp3 () : Lemma(~true == False) = ()
let bool_simp4 () : Lemma(~false == True) = ()


assume val ifte : #(a:Type) -> (c:Type0) -> (t:a) -> (e:a) -> a

let largest_single c f : 
Lemma(largest (fun (p:pr) -> c ==> f p) == ifte c (largest f) 1.0R)
[SMTPat (largest (fun (p:pr) -> c ==> f p))]
= assume False

let simp1 #a k f :
Lemma((forall k. (forall (x:a). f x ==> k x) ==> (forall (x:a). k x))
==
(forall (x:a). f x))
[SMTPat (forall k. (forall (x:a). f x ==> k x) ==> (forall (x:a). k x))]
= assume False

let probr #a (x:a) : Prob a (prob_wreturn x) by (admit_all()) = x

let simp2 #a c f :
  Lemma((forall (x:a). c == x ==> f x) == f c) = assume False

let simplify_pure_null_wp_ax1 #a : Lemma(pure_null_wp a (fun _ -> True) == True) = ()

let simplify_b2t_true () : Lemma(b2t true == True) = ()
let simplify_True_and p : Lemma((True /\ p) == auto_squash p) = ()
let simplify_and_True p : Lemma((p /\ True) == auto_squash p) = ()
let simplify_auto_squash_auto_squash p : Lemma(auto_squash (auto_squash p) == auto_squash p) = ()

let simplify_auto_squash_implies p q : Lemma((auto_squash p ==> q) == (p ==> q)) = ()
let simplify_implies_auto_squash p q : Lemma((p ==> auto_squash q) == (p ==> q)) = ()

let simplfify_eq_true b : Lemma((b = true) == b) = ()

let simplify_lift_pure_prob_wp_auto_squash f : Lemma(lift_pure_prob_wp (fun post -> auto_squash (f post)) == lift_pure_prob_wp (fun post -> f post)) = admit()

//let simplify_lift_pure_prob_wp_trivial (#a:Type) (x:a) : Lemma(lift_pure_prob_wp (fun (post:pure_post a) -> (post x)) == (fun (post:prob_post a) -> post x)) = admit()

let simplify_lift_pure_prob_wp_pure_return (#a:Type) (x:a) : Lemma(lift_pure_prob_wp (pure_return a x) == prob_wreturn x) = admit()

let simplify_pure_return (#a: Type) (x: a) :
  Lemma((fun post -> post x) == pure_return a x) = admit()

let simplify_pure_return' (#a: Type) (x: a) :
  Lemma((fun post -> auto_squash (post x)) == pure_return a x) = admit()

let pure_admit_wp (a:Type) : pure_wp a = (fun (p: pure_post a) -> True)

let simplify_cond_pure_return (#a: Type) (c: Type) (x: a) :
  Lemma((fun post -> c ==> post x) == ifte c (pure_return a x) (pure_admit_wp a)) = admit()

//let simplify_pure_return'' () : Lemma((fun post -> auto_squash (post ())) == pure_return unit ()) = simplify_pure_return' ()

let ifte_lift (#a:Type) (#b:Type) (f:a->b) (c:Type) (x y: a) : Lemma(f (ifte c x y) == ifte c (f x) (f y)) = admit()


assume val prob_admit_wp : (a:Type) -> prob_wp a (* infinity *)

let ifte_lift_lift_pure_prob_wp (#a:Type) (c:Type) (x y: pure_wp a) :
  Lemma(lift_pure_prob_wp (ifte c x y) == ifte c (lift_pure_prob_wp x) (lift_pure_prob_wp y)) 
  = ifte_lift lift_pure_prob_wp c x y


let ifte_lift_prob_wbind (#a:Type) (#b:Type) (c:Type) (x y: prob_wp a) (wp2:a->prob_wp b):
  Lemma(prob_wbind (ifte c x y) wp2 == ifte c (prob_wbind x wp2) (prob_wbind y wp2)) 
  = admit()

(*let tmp c = ifte_lift_prob_wbind c
  (lift_pure_prob_wp (pure_return unit ())) (prob_admit_wp unit)
                  (fun _ x -> prob_wreturn 0 x)*)

let simplify_if (#a:Type) (c:bool) (t e: bool->a) :
  Lemma((if c then t c else e c) == (if c then t true else e false)) = ()

let lift_pure_prob_wp_pure_admit_wp a : 
  Lemma(lift_pure_prob_wp (pure_admit_wp a) == prob_admit_wp a) = admit()

let prob_wbind_prob_admit (#a:Type) (#b:Type) (wp2:a->prob_wp b) :
  Lemma(prob_wbind (prob_admit_wp a) wp2 == prob_admit_wp b) = admit()

let rec simplifier () : Tac unit =
  l_to_r [`simplify_if];
  l_to_r [`simplify_pure_null_wp_ax1];
  l_to_r [`simplify_lift_pure_prob_wp_pure_return];
  l_to_r [`simplfify_eq_true];
  l_to_r [`simplify_pure_return];
  l_to_r [`simplify_pure_return'];
  l_to_r [`simplify_cond_pure_return];
  l_to_r [`ifte_lift_lift_pure_prob_wp];
//  l_to_r [`lift_pure_prob_wp_pure_admit_wp];
  l_to_r [`ifte_lift_prob_wbind];
//  l_to_r [`prob_wbind_prob_admit];
//  l_to_r [`bind_return];

  ()
//  if goal = cur_goal() then ()
//  else simplifier()
//
let test8a c : Prob nat 
//(prob_wreturn (if c then 0 else 1))
(fun post -> 0.0R)
by (
dump"before";
simpl ();
  l_to_r [`simplify_if];
  l_to_r [`simplify_pure_null_wp_ax1];
  l_to_r [`simplify_lift_pure_prob_wp_pure_return];
  l_to_r [`simplfify_eq_true];
  l_to_r [`simplify_pure_return];
  l_to_r [`simplify_pure_return'];
  l_to_r [`simplify_cond_pure_return];
  l_to_r [`ifte_lift_lift_pure_prob_wp];
  l_to_r [`lift_pure_prob_wp_pure_admit_wp];
//simplifier ();
//simpl ();
//simplifier ();
simpl ();
  l_to_r [`ifte_lift_prob_wbind];

(*
 prob_wbind (ifte c (lift_pure_prob_wp (pure_return unit ())) (prob_admit_wp unit))
                  (fun _ x -> prob_wreturn 0 x)
              else
              *)
              
dump"test8a";
admit_all()) =
  if c then probr 0 else probr 1



// FAILS
let test8 () : Prob nat (fun p -> (p 0 +. p 1) /. two) by (
split();
smt();
split();
split();
let c = forall_intro() in
unfold_def(`pure_null_wp);
smt();
unfold_def(`pure_null_wp);
smt();


squash_intro();
dump"before";
apply_lemma (`strongerI);
norm[];
let post = forall_intro() in
norm [delta_only ["ProbabilismWP.prob_wbind"]];
l_to_r [`on_beta];
//l_to_r [`prob_wbind_beta];
norm [simplify];
l_to_r [`bool_simp1; `bool_simp2; `bool_simp3; `bool_simp4];
norm [simplify];
l_to_r[`largest_single; `simp1; `simp2];
norm [simplify];

dump"";
admit_all() ) =
   let c : bool = coin() in 0 // (if c then 0 else 1)

// FAILS
// let test9 () : Prob bool (fun post -> (post true +. post false) /. two) =
//   (if coin () then coin() else coin())

// FAILS
// let test10 () : PROB nat (fun p -> (p 0 +. p 1) /. two) =
//   let c : bool = coin() in
//   (if true then 0 else 1)


(* 

Question:

what happens if we try to build the uniform distribution on sequences?

Approach:

let f n : Prob bool = uniform ()
let g () : Prob (nat => bool) = "f on all points" --- Doesn't work, so probably we don't have a problem.

*)
