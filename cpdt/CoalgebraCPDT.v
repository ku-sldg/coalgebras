Require Import List.

Set Implicit Arguments.

Section stream.
  Variable A:Type.

  CoInductive stream : Type :=
  | Cons : A -> stream -> stream.
End stream.

CoFixpoint zeros: stream nat := Cons 0 zeros.

CoFixpoint trues_falses: stream bool := Cons true falses_trues
with falses_trues : stream bool := Cons false trues_falses.

Fixpoint approx A (s:stream A)(n:nat) : list A :=
  match n with
  | 0 => nil
  | S n' => match s with
           | Cons h t => h :: approx t n'
           end
  end.

Eval simpl in approx zeros 10.

Eval simpl in approx trues_falses 10.

Section map.
  Variables A B : Type.
  Variable f : A -> B.

  CoFixpoint map (s:stream A): stream B :=
    match s with
    | Cons h t => Cons (f h) (map t)
    end.
End map.

Fixpoint even(n:nat):bool :=
  match n with
  | 0 => true 
  | (S 0) => false 
  | (S (S n)) => (even n)
  end.

Eval compute in map even zeros.

Section interleave.
  Variable A : Type.
  
  CoFixpoint interleave (s1 s2 : stream A):stream A :=
    match s2,s2 with
    | Cons h1 t1, Cons h2 t2 => Cons h1 (Cons h2 (interleave t1 t2))
    end.
End interleave.

(** It would seem this function fails because it touches or evaluates a stream.
 One can safely look at some finite part of the stream, but looking at the
 stream itself is a problem.  Lazy programming all over again.  Haskell
 will let you look at a finite prefix of an infinite data structure, but
 not the infinite data structure.  Coq seems to do the same thing it its
 own way.

Section map'.
  Variables A B : Type.
  Variable f : A -> B.

  CoFixpoint map'(s:stream A):stream B :=
    match s with
    | Cons h t => interleave (Cons (f h) (map' t)) (Cons (f h) (map' t))
    end.
End map'.

CoFixpoint map' (s : stream A) : stream B :=
  match s with
  | Cons h t => Cons (f h) (Cons (f h) (interleave (map' t) (map' t)))
  end.
 *)

CoFixpoint ones: stream nat := Cons 1 ones.
Definition ones' := map S zeros.

Theorem ones_eq : ones = ones'.
Proof.
  unfold ones.  unfold ones'.
Abort.

Section stream_eq.
  Variable A : Type.

  CoInductive stream_eq: stream A -> stream A -> Prop :=
  | Stream_eq: forall h t1 t2,
      stream_eq t1 t2 -> stream_eq (Cons h t1) (Cons h t2).
End stream_eq.

Definition frob A (s:stream A) : stream A :=
  match s with
  | Cons h t => Cons h t
  end.

Theorem frob_eq: forall A (s:stream A), s = frob s.
  intros. destruct s. reflexivity.
Qed.

Theorem ones_eq' : stream_eq ones ones'.
  cofix.
  rewrite (frob_eq ones).
  rewrite (frob_eq ones').
  simpl.
  constructor.
  assumption.
Qed.