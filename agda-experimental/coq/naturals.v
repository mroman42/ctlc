Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Fixpoint add (n m : nat) : nat :=
  match n with
  | O => m
  | S n => add n m
  end.

Notation "a + b" := (add a b).

Lemma plus_zero_r (n : nat) :
  n + O = n.
Proof.
  induction n.
  - reflexivity.
  - 
