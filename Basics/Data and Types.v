(*Explicit a type*)
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.
  
  
Inductive bool : Type := 
  | true
  | false.
  

(*Example definition of a function
Types here are defined explicitly but Coq can often figure out
types itself when they are not given explicitly*)
Definition next_weekdays (d : day) : day := 
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.
  
Definition negb (b:bool) : bool :=
  match b with 
  | true => false
  | false => true
  end.
  
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
  
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.
  
Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

(*Having a function, we can check how it works on some examples.
There are basically three methods to do that.
The first one uses the command Compute to evaluate a compound expression
involving next_weekdays*)
Compute (next_weekdays friday).
Compute (next_weekdays (next_weekdays saturday)).
  
(*Second, we can record what we expect the result to be.
This declaration does two things : it makes an assertion and 
it gives an assertion a name that can be used to refer to it later*)
Example test_next_weekday:
  (next_weekdays(next_weekdays saturday)) = monday.
Proof. simpl. reflexivity. Qed.
 
Definition nandb (b1:bool) (b2:bool) : bool :=
  if andb b1 b2 then false
  else true.
Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(*Types 
Every expression in Coq has a type describing what sort of thing it computes
The Check command asks Coq to print the type of an expression*)
Check true.

(*New Types from old
The types we have defined so far are examples of "enumerated
types": their definitions explicitly enumerate a finite set of elements 
called constructors. Here is a more interesting type definition,
where one of the constructors takes an argument*)

Inductive rgb : Type :=
  | red
  | green
  | blue.
  
Inductive color : Type := 
  | black
  | white
  | primary (p : rgb).
  
(*An inductive definition does two things:
1. defines a new set of constructors
2. it groups them into a new name type

We can define functions on colors using pattern matching just as we did for day and bool*)

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
