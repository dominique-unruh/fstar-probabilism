module ProbabilismWP

(* Approach with post -> real WP and with supremum axiom *)

open FStar.Real
open FStar.Tactics
open FStar.Tactics.Builtins
// open FStar.IndefiniteDescription
// open FStar.FunctionalExtensionality

let pr = r:real{r >=. zero}
let prob_post (a:Type) = a -> Tot pr
// TODO: add monotonicity
let prob_wp (a:Type) = prob_post a -> pr

assume type distribution (a:Type) : Type

assume val point_distribution (#a:Type) (x:a) : distribution a

assume val uniform_distribution (#a:Type) (x:list a{Cons? x}) : distribution a

let prob_wp_eqI #a (wp1 wp2: prob_wp a) :
    Lemma (requires (forall post. wp1 post = wp2 post))
          (ensures (wp1 == wp2)) = admit()

let prob a (w:prob_wp a): Tot Type0 =
  distribution a // TODO: require w to hold

let prob_wreturn #a x : prob_wp a = (fun post -> post x)

let prob_return a (x:a) : prob a (prob_wreturn x) = 
  point_distribution x

let prob_wbind #a #b (w1:prob_wp a) (w2:a -> prob_wp b) : prob_wp b = 
  fun post -> w1 (fun x -> w2 x post)

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
//reifiable
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

assume val inf (#a:Type) (p: a -> pr) : pr

let lift_pure_prob_wp #a (wp:pure_wp a) : prob_wp a =
    (fun (post:prob_post a) -> largest (fun (p:pr) -> wp (fun x -> p <=. post x)))

let lift_pure_prob a (wp:pure_wp a) (f: eqtype_as_type unit -> PURE a wp) : 
   prob a (lift_pure_prob_wp wp) =
   assume False; // TODO
   point_distribution (f ())

sub_effect PURE ~> PROB = lift_pure_prob

(* let lift_div_prob a (wp:pure_wp a) (f: eqtype_as_type unit -> DIV a wp) : 
   prob a (lift_pure_prob_wp wp) =
   assume False; // TODO
   //point_distribution (f ())
   admit()

sub_effect DIV ~> PROB = lift_div_prob *)

effect ProbAny (a:Type) = PROB a (fun post -> 0.0R)

let coin () : PROB bool (fun (post) -> (post true +. post false) /. two) =
  PROB?.reflect (uniform_distribution [true;false])

let test1 () : PROB bool (fun post -> (post true +. post false) /. two) = coin ()

let test2 () : ProbAny bool = coin ()

let test3 x : PROB string (prob_wreturn x) 
by (admit_all()) = assume False; x

let test4 () : PROB string (prob_wreturn "hello") = test3 "hello"

let f (b:bool) : nat = if b then 0 else 1

irreducible
let bind_return #a #b (wp1:prob_wp a) (f:a->b) : 
    Lemma(prob_wbind wp1 (fun x -> prob_wreturn (f x))
                      == (fun(post:prob_post b) -> wp1 (fun x -> post (f x))))
  [SMTPat (prob_wbind wp1 (fun x -> prob_wreturn (f x)))]                                 
        =
  admit()				     

irreducible
let return_bind #a #b (x:a) (wp2:a -> prob_wp b) : Lemma(prob_wbind (prob_wreturn x) wp2 == wp2 x) 
  [SMTPat (prob_wbind (prob_wreturn x) wp2)]
  =
  admit()

let test5 () : PROB nat (fun post -> (post 0 +. post 1) /. two) =
  let c : bool = coin() in
  f c

(*let prob_wbind_on #a #b (wp1:prob_wp a) (wp2:a -> prob_wp b) : 
  Lemma(prob_wbind (on (prob_post a) #pr wp1) wp2 == prob_wbind wp1 wp2)
  [SMTPat (prob_wbind (on _ wp1) wp2)]
  = () *)

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

let test6 () : PROB nat (fun p -> p 0)
=
  let c : bool = coin() in 0

// let on_beta #a #b (f:_->_) x : Lemma(on a #b f x == f x) = ()

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

(* let simp1 #a k f :
Lemma((forall k. (forall (x:a). f x ==> k x) ==> (forall (x:a). k x))
==
(forall (x:a). f x))
[SMTPat (forall k. (forall (x:a). f x ==> k x) ==> (forall (x:a). k x))]
= assume False *)

let probr #a (x:a) : PROB a (prob_wreturn x) by (admit_all()) = x

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

let simplfify_eqq_true b : Lemma((b == true) == b2t b) = admit()

let simplify_lift_pure_prob_wp_auto_squash f : Lemma(lift_pure_prob_wp (fun post -> auto_squash (f post)) == lift_pure_prob_wp (fun post -> f post)) by (admit_all()) = ()

//let simplify_lift_pure_prob_wp_trivial (#a:Type) (x:a) : Lemma(lift_pure_prob_wp (fun (post:pure_post a) -> (post x)) == (fun (post:prob_post a) -> post x)) = admit()

let simplify_lift_pure_prob_wp_pure_return (#a:Type) (x:a) : Lemma(lift_pure_prob_wp (pure_return a x) == prob_wreturn x) by (admit_all()) = admit()

let simplify_pure_return (#a: Type) (x: a) :
  Lemma((fun post -> post x) == pure_return a x) = admit()

let simplify_pure_return' (#a: Type) (x: a) :
  Lemma((fun post -> auto_squash (post x)) == pure_return a x) = admit()

let pure_admit_wp (a:Type) : pure_wp a by (admit_all()) = (fun (p: pure_post a) -> True)

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

let if_ifte1 (#a:Type) (c:bool) (x y z:a) :
    Lemma((if c then ifte c x y else z) == (if c then x else z)) = admit()

let simp_forall_x_xeqc_fx (#a:Type) (c:a) f :
    Lemma((forall (x:a). x == c ==> f x) == f c) = admit()
let simp_forall_x_ceqx_fx (#a:Type) (c:a) f :
    Lemma((forall (x:a). c == x ==> f x) == f c) = admit()

let simp_forall_k (#a:Type) f g :
    Lemma((forall k. (forall (x:a). f x ==> k x) ==> g k) == g f)
    = admit()

let simp_fun_ite (#a:Type) c f g :
    Lemma((fun p -> (c ==> f p) /\ (~c ==> g p)) == ifte c f g)
    = admit()

(*
/// Runs tac and returns whether tac changed the goal.
/// Assumes that only the current goal is affected and that the current goal is not removed
let changed_tac (tac: unit -> Tac unit) : Tac bool =
    let goal = cur_goal () in
    tac ();
    let goal2 = cur_goal () in
    not (term_eq goal goal2)
*)

let ifte_inline (#a:Type) c (d:Type->a) (e:Type->a) :
  Lemma(ifte c (d c) (d c) == ifte c (d True) (d False)) = admit()

// (lift_pure_prob_wp (fun post -> forall (any_result: nat). post any_result))

//let lift_pure_prob_wp #a (wp:pure_wp a) : prob_wp a =
//    (fun (post:prob_post a) -> largest (fun (p:pr) -> wp (fun x -> p <=. post x)))

let lift_pure_prob_wp_inf (#a:Type) :
  Lemma(lift_pure_prob_wp (fun post -> forall (x: a). post x)
     == (fun (post: prob_post a) -> inf post))
     by (admit_all())
     = ()

assume val ifte_True (a:Type) (x:a) (y:a) : Lemma(ifte True x y == x)

let simplifier1 () : Tac unit =
  l_to_r [`simplify_pure_null_wp_ax1];
  l_to_r [`simplify_lift_pure_prob_wp_pure_return];
  l_to_r [`simplfify_eq_true];
  l_to_r [`simplfify_eqq_true];
  l_to_r [`simplify_pure_return];
  l_to_r [`simplify_pure_return'];
  l_to_r [`simplify_cond_pure_return];
  l_to_r [`ifte_lift_lift_pure_prob_wp];
  l_to_r [`lift_pure_prob_wp_pure_admit_wp];
  l_to_r [`ifte_lift_prob_wbind];
  l_to_r [`prob_wbind_prob_admit];
  l_to_r [`if_ifte1];
  l_to_r [`lift_pure_prob_wp_inf];
  l_to_r [`return_bind];
  l_to_r [`simp_forall_x_xeqc_fx];
  l_to_r [`simp_forall_x_ceqx_fx];
  l_to_r [`simp_forall_k];
  l_to_r [`simp_fun_ite];
  l_to_r [`ifte_True];
  ()

let forget_result #a #b (tac: a -> Tac b) x : Tac unit = let _ = tac x in ()

let auto_squash_intro_lemma (#a: Type) (x: squash a) : squash (auto_squash a) = ()

let auto_squash_intro () : Tac unit = apply(`auto_squash_intro_lemma)

/// Assumes a focused goal
let rec intros () : Tac unit =
    match term_as_formula (cur_goal ()) with
      | Implies _ _ -> let _ = implies_intro () in intros ()
      | Forall _ _ -> let _ = forall_intro () in intros ()
      | True_ -> trivial ()
      | And _ _ -> split(); iterAll intros
      | App hd _ ->
      	  (match inspect hd with
	    | Tv_FVar const ->
	        let qn = inspect_fv const in
                if qn = squash_qn then (squash_intro(); intros())
	    	else if qn = ["Prims"; "auto_squash"]
	    	then (auto_squash_intro (); intros())
	        else ()
            | _ -> ())
      | _ -> ()


(*let rec intros () : Tac bool =
    let one = split <|> forget_result implies_intro <|> forget_result forall_intros <|> double_squash_intro <|> trivial in
    try one (); iterAll (forget_result intros); true
    with | _ -> false *)

let rec simplifierFocused () : Tac unit =
  dump "starting simplifier";
  simpl();
  dump "simpl done";
  let _ = intros() in
  dump "intros done";
  iterAll simplifierFocused'

and simplifierFocused' () : Tac unit =
  let goal = cur_goal () in
  simplifier1 ();
  let goal2 = cur_goal () in
  if (term_eq goal goal2)
  then ()
  else iterAll simplifierFocused

let simplifier () : Tac unit =
  focus simplifierFocused

let simplifierAll () : Tac unit =
  iterAll simplifierFocused

let unfold_tac () : Tac unit = norm [delta_qualifier ["unfold"]]

let test8a c : PROB nat (fun post -> if c then post 0 else post 1)
   by (simplifier(); cases_bool (quote c); simplifierAll(); dump""; unfold_tac()) =
  if c then probr 0 else probr 1



let test8b c : PROB nat (fun post -> if c then post 0 else post 1)
   by (cases_bool (quote c);
       simplifierAll();
       dump "") =
  if c then 0 else 1


//let strengthen (a b:Type) (p:a -> ProbAny b) (wp:a -> prob_wp b) : (q:(x:a -> PROB b (wp x)){p==q}) = assume False; p

// FAILS
let test8 () : PROB nat (fun p -> (p 0 +. p 1) /. two) by (
simplifier();
//l_to_r [`ifte_inline];
smt();
smt();
smt();
dump"";
admit_all();
()
) =
   let c : bool = coin() in (if c then 0 else 1)

// FAILS
let test9 () : PROB bool (fun post -> (post true +. post false) /. two) =
  (if coin () then coin() else coin())

// FAILS
let test10 () : PROB nat (fun p -> (p 0 +. p 1) /. two) =
  let c : bool = coin() in
  (if true then 0 else 1)


(* 

Question:

what happens if we try to build the uniform distribution on sequences?

Approach:

let f n : Prob bool = uniform ()
let g () : Prob (nat => bool) = "f on all points" --- Doesn't work, so probably we don't have a problem.

*)
