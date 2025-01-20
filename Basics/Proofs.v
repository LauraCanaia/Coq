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

  (*PROOF BY CASE ANALYSIS
In general, hypothetical values can block semplification.
To make progress, we need to consider the possible forms of n separately. If
n is 0, then we can calculate the final result of (n+1)  =? 0 and check that it is false. 
And if n = S n' for some n', then we can calculate at least it will begin with one S.*)

Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | O, S _ => false
  | S _, O => false
  | S n', S m' => eqb n' m'
  end.

Notation "x =? y" := (eqb x y) (at level 70).

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1 =? 0) = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Definition negb (b:bool) : bool :=
  match b with 
  | true => false
  | false => true
  end.

(*The destruct generates two subgoals, which must then prove separately in order to get coq accept the theorem.

The annotation as [| n'] is called INTRO PATTERN. It tells Coq what variable names to introduce in each subgoal.
In general what goes between the square brakets s a list of lists of names separated by |.

The eqn:E annotation tells destruct to give the name E to this equation.

The - signs on the lines 21 and 22 are called bullets, and they mark the parts of the proof that correspond to the two 
generated subgoals. The part of the proof that correspond to the two generated subgoals. The part of the proof script that
comes after a bullet is the entire proof for the corresponding subgoal.
Each of the subgoals is easily proved by a single use of reflexivity, wich of the subgoals preforms some sort of semplification.*)

(*The destruct tactic can be used with any inductively defined datatype. For example, we use it next to prove that boolean negation is involutive -
i.e. that negation is its own inverse*)

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn : E.
  - reflexivity.
  - reflexivity. 
Qed.

(*It is sometimes useful to invoke destruct inside a subgoal, generating yet more proof obligations.
In this case, we use different kinds of bullets yo mark goals on different "levels". For example:*)

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn : Eb.
  -destruct c eqn : Ec.
    + reflexivity.
    + reflexivity.
  -destruct c eqn : Ec.
    + reflexivity.
    + reflexivity.
Qed.

(*We can also use curly braces*)

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn : Eb.
  - destruct c eqn : Ec.
  {destruct d eqn :Ed.
    - reflexivity.
    - reflexivity. }
  {destruct d eqn :Ed.
    - reflexivity.
    - reflexivity. }
  - destruct c eqn : Ec.
  {destruct d eqn :Ed.
    - reflexivity.
    - reflexivity. }
  {destruct d eqn :Ed.
    - reflexivity.
    - reflexivity. }
Qed.

(*EXERCISE*)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. 
  intros H.
  destruct b.
  (*CASE b = true*)
    - destruct c.
      (*CASE c = true*)
      + rewrite <- H. reflexivity.
      (*CASE c = false*)
      + rewrite <- H. reflexivity.
  (*CASE b = false*)
    - destruct c.
      (*CASE c = true*)
      + rewrite <- H. reflexivity.
      (*CASE c = false*)
      + rewrite <- H. reflexivity.
Qed.

