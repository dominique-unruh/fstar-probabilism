(* Attempt to define the PURE effect, following the paper "Layered Indexed Effects" *)
(* Tried with F* 0.9.7.0-alpha1 *)

module Pure

let wp t = (t -> prop) -> prop
unfold let wreturn x = fun p -> p x
unfold let wbind w1 w2 = fun p -> w1(fun x -> w2 x p)
let pure (a:Type) (w:wp a) : Type = p:(a -> prop) -> squash (w p) -> Tot (v:a{p v})

let check a (x:a) = ()
let cast a (x:a) : a = x
let claim a (#p:squash a) : squash a = p

// I had to add some extra hints to make this typecheck. Should be equivalent to what's in the paper, though
let return (a:Type) (x:a) : pure a (wreturn x) = fun p (_:squash (wreturn x p)) -> cast (v:a{p v}) x


let bind (a b:Type) (w1:wp a) (w2:(a -> wp b)) (f: pure a w1) (g: (x:a -> pure b (w2 x))) : 
                           pure b (wbind w1 w2) = 
    fun p _ -> let x = f (fun x -> w2 x p) () in g x p ()


layered_effect {
  PURE : a:Type -> w:wp a -> Effect 
    with
    repr = pure; return = return; bind = bind 
}
