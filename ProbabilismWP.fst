(*

This file sketches the modeling and use of the PROB effect based on
the wp-approach.

The main aim was to explore how the effect can be defined, and also
how one can type functions.

All the lemmas that are used are unproven so far.

In fact, I believe the file is not really consistent because I
sometimes switch between seeing postconditions as using non-negative
reals, and sometimes as using non-negative extended reals, i.e.,
including infinity. (E.g., in prob_admit_wp.)

Main work/trouble was trying to get a simplifier for solving
typing-VCs.

*)

module ProbabilismWP

open FStar.Real
open FStar.Tactics
open FStar.Tactics.Builtins

// Non-negative reals (pr like probability is a slight misnomer
// because we do not upper bound it by 1)
let pr = r:real{r >=. zero}

// Post-condition type
let prob_post (a:Type) = a -> Tot pr

// Weakest precondition type
// TODO: add suitable monotonicity constraints as refinement
let prob_wp (a:Type) = prob_post a -> pr

// Models a probability distribution, basically (f:a -> pr){sum <= 1}
assume type distribution (a:Type) : Type

// Distribution that gives probability 1 to x
assume val point_distribution (#a:Type) (x:a) : distribution a

// Uniform distribution on x (must be a non-empty list)
assume val uniform_distribution (#a:Type) (x:list a{Cons? x}) : distribution a

// Simple auxiliary lemma for showing equality of two wp's
let prob_wp_eqI #a (wp1 wp2: prob_wp a) :
    Lemma (requires (forall post. wp1 post = wp2 post))
          (ensures (wp1 == wp2)) = admit()

// Representation type for PROB effect.
// "prob a w" is the type of distributions f over a that satisfy the wp w.
// (I.e., they satisfy "forall post, sum_{x:a} f(x)post(x) >= w(post).)
// TODO: A refinement has to be added with that condition
let prob a (w:prob_wp a): Tot Type0 =
  distribution a // TODO: require w to hold

// Wp corresponding to "prob_return x"
let prob_wreturn #a x : prob_wp a = (fun post -> post x)

// Semantics of "return x"
let prob_return a (x:a) : prob a (prob_wreturn x) = 
  point_distribution x

// Wp corresponding to "let x = p1 in p2 x", given the wps for p1, p2
let prob_wbind #a #b (w1:prob_wp a) (w2:a -> prob_wp b) : prob_wp b = 
  fun post -> w1 (fun x -> w2 x post)

// TODO: document or remove
let prob_wbind_beta #a #b (w1:prob_wp a) (w2:a -> prob_wp b) (post:prob_post b) :
  Lemma (prob_wbind w1 w2 post == w1 (fun x -> w2 x post)) = ()

// Semantics of "let x = p1 in p2 x"
let prob_bind a b (w1:prob_wp a) (w2:a -> prob_wp b)
      (f: prob a w1) (g: (x:a -> prob b (w2 x))) : prob b (prob_wbind w1 w2) =
   admit()   

// w1 is a more restrictive wp than w2
let stronger #a (w1 w2:prob_wp a) = forall post. w1 post >=. w2 post

// TODO: document or remove
let strongerI #a (w1 w2:prob_wp a) :
  Lemma (requires forall post. w1 post >=. w2 post)
        (ensures w1 `stronger` w2) = ()

// TODO: document or remove
let prob_wp_stronger_eq #a (w1 w2:prob_wp a) :
    Lemma (requires w1 `stronger` w2 /\ w2 `stronger` w1)
    	  (ensures w1 == w2) = 
    assert (w1 == w2) by (apply_lemma (`prob_wp_eqI))

// Weakening in the PROB effect: takes "f:prob a w1" and returns the same f with a different type "prob a w2",
// assuming w2 is a weaker wp than w2
let prob_subcomp a (w1 w2 : prob_wp a) (f:prob a w1) : 
                 Pure (prob a w2) (requires w1 `stronger` w2) (ensures (fun _ -> True)) =
  f

// Semantics of if-then-else in a probabilistic program.
// Since the condition is a fixed boolean, this is quite trivial.
let ite_prob a (#w1 #w2 : prob_wp a) (f: prob a w1) (g: prob a w2) (b: bool) : Type =
  prob a (if b then w1 else w2)

// Defining the PROB effect. Representation type is prob, and the
// effect is defined using the various specifications of the semantics
// that we defined above.
total
reflectable // Means we can create a probabilistic function from an explicitly given distribution. See coin below.
//reifiable
layered_effect { PROB : (a:Type) -> (wp:prob_wp a) -> Effect with 
  repr = prob;
  return = prob_return; 
  bind = prob_bind;
  subcomp = prob_subcomp;
  if_then_else = ite_prob
  }

// TODO: document or remove
assume val real_numbers_complete: unit -> Lemma(
  forall (p: real->bool) low high.
  p low ==> not (p high) ==> (forall x y. x >=. y ==> p x ==> p y) ==>
  (exists sup. (forall x. x <. sup ==> p x) /\ (forall x. x >. sup ==> not (p x))))


// "largest p" is the largest real satisfying p
// TODO: Add ensures to state that it returns the largest real
// TODO: Add requires to enforce conditions of p that are needed for that real to exist
assume val largest (p: pr -> Type0) : pr

// "inf p" returns the infimum of {p x. x:a}
// TODO: Add ensures/requires
assume val inf (#a:Type) (p: a -> pr) : pr

// Given PURE-wp wp, this returns the corresponding wp of the
// probabilistic program.  I.e., if f:PURE wp, then "return f : PROB
// (lift_pure_prob_wp wp)", roughly speaking.  Note that this is the
// place where we use "largest" whose existence is (I think)
// equivalent to the strong excluded middle, and which is the reason
// why I favor the Hoare-approach instead.
let lift_pure_prob_wp #a (wp:pure_wp a) : prob_wp a =
    (fun (post:prob_post a) -> largest (fun (p:pr) -> wp (fun x -> p <=. post x)))

// Given pure program f, returns the corresponding probabilistic program "return f"
let lift_pure_prob a (wp:pure_wp a) (f: eqtype_as_type unit -> PURE a wp) : 
   prob a (lift_pure_prob_wp wp) =
   assume False; // TODO
   point_distribution (f ())

// Using lift_pure_prob, we tell F* how to transform a PURE effect
// into a PROB effect.  Interestingly, without this, almost nothing
// works. Even very simple functions fail without this (e.g., test0
// below). This is a bit strange because I would expect that
// prob_return would beused for giving meaning to that
// function. Apparently not, so I wonder what prob_return is used for
// by "effect".
sub_effect PURE ~> PROB = lift_pure_prob

// Does not work without the sub_effect above
let test0 () : PROB bool (fun post -> zero) = true

// A wrapper effect. ProbAny is PROB with trivial wp, i.e., "ProbAny
// a" is always a valid type for a probabilistic program returning a.
effect ProbAny (a:Type) = PROB a (fun post -> 0.0R)

// A basic function for writing probabilistic programs. Returns a random bool.
// The type characterizes this.
let coin () : PROB bool (fun (post) -> (post true +. post false) /. two) =
  PROB?.reflect (uniform_distribution [true;false])

// Testing if things work
let test1 () : PROB bool (fun post -> (post true +. post false) /. two) = coin ()

// Testing if things work
let test2 () : ProbAny bool = coin ()

// XXXXXXXXXXXXXX


// Attempt at telling SMT how to simplify a bind-return combination.
// But the SMTPat gives a warning, so probably the match is too
// higher-order for SMT
(* assume val bind_return (#a #b:Type) (wp1:prob_wp a) (f:a->b) : 
    Lemma(prob_wbind wp1 (fun x -> prob_wreturn (f x))
                      == (fun(post:prob_post b) -> wp1 (fun x -> post (f x))))
  [SMTPat (prob_wbind wp1 (fun x -> prob_wreturn (f x)))] *)

// Attempt at telling SMT how to simplify return-bind combination.
// Don't know if it works.
assume val return_bind (#a #b:Type) (x:a) (wp2:a -> prob_wp b) : Lemma(prob_wbind (prob_wreturn x) wp2 == wp2 x) 
  [SMTPat (prob_wbind (prob_wreturn x) wp2)]

// Testing if things work.
// Interestingly, if we inline f here, this does not immediately typecheck any more (see test8b).
let f (b:bool) : nat = if b then 0 else 1
let test5 () : PROB nat (fun post -> (post 0 +. post 1) /. two) =
  let c : bool = coin() in f c

// Testing if things work.
let test6 () : PROB nat (fun p -> p 0) =
  let c : bool = coin() in 0

//let bool_simp1 () : Lemma((true = true) == true) = ()
//let bool_simp2 () : Lemma((false = true) == false) = ()
//let bool_simp3 () : Lemma(~true == False) = ()
//let bool_simp4 () : Lemma(~false == True) = ()


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


// TODO: remove admit_all
// TODO: move down to the failing things
let test3 x : PROB string (prob_wreturn x) by (admit_all()) = assume False; x

let test4 () : PROB string (prob_wreturn "hello") = test3 "hello"


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

