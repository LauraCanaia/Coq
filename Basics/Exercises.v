(*EXERCISE 1*)

Theorem identify_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) -> forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

(* In the previous exercise I'm doing the following simplifications:
With intros f H b I'll have one goal:
f : bool -> bool 
H : forall x : bool, f x = x
b : bool

rewrite -> H: from f (f b) = b I'll go to f b = b

rewrite -> H: from f b = b I'll go to b = b and with refexivity I'll demonstrate the proof*)
