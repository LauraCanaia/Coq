(*PROOF BY SIMPLIFICATION
- Can be used to establish more interesting properties
- For example the fact that 0 is a neutral element for + onthe left can be proved just by observing that 0 + n reduces to n
no matter wht n is*)

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.
  
(*Reflexivity does somewht more simplification that simpl does. If reflexivity succeds, the whole goal is finished and we don't
need to look at whatever expanded expressions reflexivity has created by all this simplification and unfolding; by contrast, simpl
is used in situations where may have to read and understand the new goal that it creates.*)

Theorem plus_0_n'' : forall n : nat, 0 + n = n.
Proof.
  intros m. reflexivity. Qed.
  
(*The keywords intros, simpl, and reflexivity are examples of tactics. A tactic is a command that is used between Proof and Qed to
guide the process of checking some claim we are making.
Other similar theorems can be orived with the same pattern.*)

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof. 
  intros n. reflexivity. Qed.
  
Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.
  
(*PROOF BY REFLEXIVITY
Instead of making a universal claim about all numbers n and m, it talks about a more specialized property that only holds when n = m.
The arrow symbol is pronounced "implies".
As before we need to be able to reason by assuming we are given such numbers n and m and we also need to assume the hypothesis n = m.
The intros tactic will serve to move all three of these from the goal into assumptions in the current context.

Since n and m are arbitrary numbers, we can't just use simplification to prove this theorem. Instead, we prove it by observing that, if
we are assuming n = m, then we can replace n with m in the goal statement and obtain an equality with the same expression on both sides.
The tactic that tells Coq to perform this replacement is called rewrite.*)

Theorem plus_id_example : forall n m : nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity. Qed.
  
(*Exercise*)
Theorem plus_id_exercise : forall n m o : nat,
  n = m ->
  m = o ->
  n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity. Qed.
(*----------------------------*)

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.
  
(*Exercise*)
Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  rewrite -> plus_0_n.
  reflexivity. Qed.
(*----------------------------*)
