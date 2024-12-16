
(*Modules
Coq provdes a module system to aid in organizing large developments.
We don't need most of its features, but one is useful here: if we enclose a collection of declarations
between module X and End X markers, then these definitions are referred to by names like X.foo.
We will use this feature to limit the scope of definitions, so that we are free to reuse names*)

Inductive bool : Type := 
  | true
  | false.
  
Inductive rgb : Type :=
  | red
  | green
  | blue.
  
Inductive color : Type := 
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c : color) : bool := 
  match c with 
  | black => true
  | white => true
  | primary p => false
  end.
  
Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.
  
Module Playground.
  Definition foo : rgb := blue.
End Playground.

Definition foo : bool := true.

Check Playground.foo : rgb.
Check foo : bool.

(*Tuples
A single contructor with multiple parameters can be used to create a tuple type.
Consider representing in four bits a nybble. We first define a datatype bit that
resembles bool and then define the datatype nybble -> essentially a tuple of four bits*)

Inductive bit : Type :=
  | B1
  | B0.
  
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).
  
Check (bits B1 B0 B1 B0)
  : nybble.
  
(*Numbers
The natural numbers are in infinite set, so we'll need to use a slightly richer form
of type declaration to represent them. Representation of unary base where a single digit
is used. To represent unary numbers with a Coq datatype, we use two constructors.
The capital-letter O constructor represents O and the S constructor can be applied to the 
representation of the natural number n.*)

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).
  
(*A critical point here is that what we've done so far is just to define a representation
of numbers: a way of writing them down. The names O and S are arbitrary, and at this point they have
no special meaning. If we like, we can rewrite the same definition this way*)

Inductive otherNat : Type :=
  | stop
  | tick (foo : otherNat).

(*The interpretation of these marks arises from how we use them to compute.

We can do this by writing functions that pattern match on representations of natural
numbers just as we did above with booleans and days.*)

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End NatPlayground.

Check (S (S (S (S O)))).

Definition minustwo (n : nat) : nat :=
  match n with  
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo 4).

(*Differently from other functions, pred and minustwo are defined by giving computations
rules while the deinition of S has no such behavior attached.
For more interesting computations involving numbers, simple pattern matching is not enough:
we also need recursion. Example: check if a number is odd or even*)

Fixpoint even (n : nat) : bool :=
  match n with 
  | O => true
  | S O => false
  | S (S n') => even n'
  end.
  
(*Defined that, we can also define odd in function of even*)

Definition negb (b:bool) : bool :=
  match b with 
  | true => false
  | false => true
  end.
  
Definition odd (n:nat) : bool :=
  negb (even n).


Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with 
  | O => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

(*Even testing equality is a user-defined operation. The following function ebp
tests natural numbers for equality, yelding a boolean.*)

Fixpoint eqb (n m : nat) : bool :=
  match n with 
  | O => match m with
        | O => true
        | S m' => false
        end
  | S n' => match m with
        | O => false
        | S m' => eqb n' m'
        end
  end.

(*Simarly we can define a leb function which returns true whether its first argument
is less then or equal to its second argument*)

Fixpoint leb (n m : nat) : bool := 
  match n with
  | O => true
  | S n' => match m with
           | O => false
           | S m' => leb n' m'
           end
  end.
  
Definition ltb (n m : nat) : bool :=
  match n with
  | O => match m with
        | O => false
        | S m' => true
        end
  | S n'=> match m with
        | O => false
        | S m' => ltb n' m'
        end
  end.
  
Compute ltb 0 5.
