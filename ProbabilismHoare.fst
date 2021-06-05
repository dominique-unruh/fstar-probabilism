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

// Non-negative reals (pr like probability is a slight misnomer
// because we do not upper bound it by 1)
let pr = r:real{r >=. zero}

// Post-condition type
let prob_post (a:Type) = a -> Tot pr

// Weakest precondition type
// TODO: maybe add suitable monotonicity constraints as refinement
let prob_wp (a:Type) = pr -> prob_post a -> Type0

// Models a probability distribution, basically (f:a -> pr){sum <= 1}
assume type distribution (a:Type) : Type

// Distribution that gives probability 1 to x
assume val point_distribution (#a:Type) (x:a) : distribution a

// Uniform distribution on x (must be a non-empty list)
assume val uniform_distribution (#a:Type) (x:list a{Cons? x}) : distribution a

// Representation type for PROB effect.
// "prob a w" is the type of distributions f over a that satisfy the wp w.
// (I.e., they satisfy "forall pre post, w pre post -> sum_{x:a} f(x)post(x) >= pre.)
// TODO: A refinement has to be added with that condition
let prob a (w:prob_wp a): Tot Type0 =
  distribution a // TODO: require w to hold

// let b2p (b: bool) : prop = b == true

//let t2p (t: Type0) : prop = t

// Wp corresponding to "prob_return x"
let prob_wreturn #a x : prob_wp a = 
    (fun (pre:pr) -> (fun (post:prob_post a) -> pre <=. post x))

// Semantics of "return x"
let prob_return a (x:a) : prob a (prob_wreturn x) = 
  point_distribution x

// Wp corresponding to "let x = p1 in p2 x", given the wps for p1, p2
let prob_wbind #a #b (w1:prob_wp a) (w2:a -> prob_wp b) : prob_wp b = 
    (fun (pre:pr) -> (fun (post:prob_post b) ->
      exists (mid:prob_post a). w1 pre mid /\ (forall (x:a). w2 x (mid x) post)))

// Semantics of "let x = p1 in p2 x"
assume val prob_bind (a b:Type) (w1:prob_wp a) (w2:a -> prob_wp b)
      (f: prob a w1) (g: (x:a -> prob b (w2 x))) : prob b (prob_wbind w1 w2)

let stronger #a (w1 w2:prob_wp a) = forall post pre. w2 post pre ==> w1 post pre

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
reifiable // Works here! (Doesn't work in ProbabilismWP because repr is "informative"
reflectable // Means we can create a probabilistic function from an explicitly given distribution. See coin below.
layered_effect { PROB : (a:Type) -> (wp:prob_wp a) -> Effect with 
  repr = prob;
  return = prob_return; 
  bind = prob_bind;
  subcomp = prob_subcomp;
  if_then_else = ite_prob
  }

// Given PURE-wp wp, this returns the corresponding wp of the
// probabilistic program.  I.e., if f:PURE wp, then "return f : PROB
// (lift_pure_prob_wp wp)", roughly speaking.
let lift_pure_prob_wp #a (wp:pure_wp a) : prob_wp a =
    fun pre post -> wp (fun x -> pre <=. post x)

// Given pure program f, returns the corresponding probabilistic program "return f"
let lift_pure_prob a (wp:pure_wp a) (f: eqtype_as_type unit -> PURE a wp) : 
   prob a (lift_pure_prob_wp wp) by (admit_all()) =
   point_distribution (f ())
   
sub_effect PURE ~> PROB = lift_pure_prob

// Helper function. Constructs a wp in the Hoare-approach (type prob_wp above) from a wp in the wp-approach.
let from_wp #a (wp: prob_post a -> pr) : prob_wp a = fun pre post -> pre <=. wp post

// A basic function for writing probabilistic programs. Returns a random bool.
// The type characterizes this.
let coin () : PROB bool (from_wp (fun post -> (post true +. post false) /. two)) =
  PROB?.reflect (uniform_distribution [true;false])

(**** TESTS *****)

// Some very simple tests (anything beyond that would probably need a simplifier like in ProbabilismWP).

let test1 () : PROB bool (from_wp (fun post -> (post true +. post false) /. two)) = coin ()

let test2 () : PROB bool (fun pre post -> False) = coin ()

// Note that this one did not typecheck in ProbabilismWP without the simplifier
let test3 x : PROB string (prob_wreturn x) = x

let test4 () : PROB string (prob_wreturn "hello") = test3 "hello"

(* None of the tricky cases are included... *)
