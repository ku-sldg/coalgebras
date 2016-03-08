Require Import List.
Require Import CpdtTactics.

Set Implicit Arguments.

(** Define a [stream] as an infinite structure with a single constructor and
  no base case.  The [CoInductive] definition is used for this creature, but
  it looks a great deal like an Inductive type without the base case. *)

Section stream.
  Variable A:Type.

  CoInductive stream : Type :=
  | Cons : A -> stream -> stream.
End stream.

(** [zeros] is a [stream] of [nat]s constructed by consing 0 onto [zeros].
  This has the feel of an infinite type in Haskell.  Even looks kind of like
  an infinite type in Haskell. *)

CoFixpoint zeros: stream nat := Cons 0 zeros.

(** Similuar mutual construction of alternating [true] and [false] values. 
  Note the use of [with] to provide two mutual definitions.  This is the
  first time I have seen this. *)

CoFixpoint trues_falses: stream bool := Cons true falses_trues
with falses_trues : stream bool := Cons false trues_falses.

(** [approx] looks at the first [n] elements of stream [s].  Note that
 [approx] does not evaluate the stream and only looks at the stream head.
 It uses [n] to define a finite prefix of [s] that is [n] elements long. *)

Fixpoint approx A (s:stream A)(n:nat) : list A :=
  match n with
  | 0 => nil
  | S n' => match s with
           | Cons h t => h :: approx t n'
           end
  end.

Eval simpl in approx zeros 10.

Eval simpl in approx trues_falses 10.

(** Stream [map] is just what you think it would be.  However, stream [map]
 cannot terminate.  Thus, you can only look at finite prefixes of the stream. 
 The reference [t], the infinite tail of [s], is *guarded* by the constructor
 [Cons].  Why does this help?  You can calculate [(f h)] on the head and
 tuck the tail into a recursive [map] call that *need not be evaluted* to 
 define the corecursive call.  This guarding is key to the definition. *)

Section map.
  Variables A B : Type.
  Variable f : A -> B.

  CoFixpoint map (s:stream A): stream B :=
    match s with
    | Cons h t => Cons (f h) (map t)
    end.
End map.

(** This is not in the book, but shows that the [map] constructs a stream that
 can be computed with using [approx] or any other similar thing that does not
 touch the infinite tail. *)

Eval compute in approx (map (fun x => (x + 1)) zeros) 10.

Fixpoint even(n:nat):bool :=
  match n with
  | 0 => true 
  | (S 0) => false 
  | (S (S n)) => (even n)
  end.

Eval compute in map even zeros.

Eval compute in approx (map even zeros) 10.

(** [interleave] does what the name implies and interleaves to streams.
  the [CoFixpoint] creates a stream that we can take a peek at later as
  long as we don't touch the tail.  Note that the call to [interleave] is
  guarded by the constructor [Cons]. *)

Section interleave.
  Variable A : Type.
  
  CoFixpoint interleave (s1 s2 : stream A):stream A :=
    match s2,s2 with
    | Cons h1 t1, Cons h2 t2 => Cons h1 (Cons h2 (interleave t1 t2))
    end.
End interleave.

Eval compute in approx (interleave zeros zeros) 10.

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

Definition hd A (s:stream A) : A :=
  match s with
  | Cons x _ => x
  end.

Definition tl A (s:stream A) : stream A :=
  match s with
  | Cons _ s' => s'
  end.

Section stream_eq_coind.
  Variable A : Type.
  Variable R : stream A -> stream A -> Prop.

  Hypothesis Cons_case_hd: forall s1 s2, R s1 s2 -> hd s1 = hd s2.
  Hypothesis Cons_case_tl: forall s1 s2, R s1 s2 -> (R (tl s1) (tl s2)).

  (** This proof is completely opaque to me.  Need to spend some time with it.
    it feels more indictive than coindictive for some reason. *)
  
  Theorem stream_eq_coind : forall s1 s2, R s1 s2 -> stream_eq s1 s2.
    cofix; destruct s1; destruct s2; intro.
    generalize (Cons_case_hd H); intro Heq; simpl in Heq; rewrite Heq.
    constructor.
    apply stream_eq_coind.
    apply (Cons_case_tl H).
  Qed.
End stream_eq_coind.

Print stream_eq_coind.

(** [intuition] and [subst] do quite a bit of work here.  [unfold] makes the
  [hd] and [tl] visible to the proof.  Thus [reflexivity] can pop things
  out quickly.  Still, the larger proof is opaque to me. *)

Theorem ones_eq'' : stream_eq ones ones'.
  apply (stream_eq_coind (fun s1 s2 => s1 = ones /\ s2 = ones')).
  intuition. subst. unfold ones. unfold ones'. reflexivity.
  intuition. subst. unfold ones. reflexivity.
  subst. unfold ones'. reflexivity.
  intuition.
Qed.

Section stream_eq_loop.
  Variable A : Type.
  Variables s1 s2 : stream A.

  Hypothesis Cons_case_hd: hd s1 = hd s2.
  Hypothesis loop1 : tl s1 = s1.
  Hypothesis loop2 : tl s2 = s2.

  Theorem stream_eq_loop: stream_eq s1 s2.
    apply (stream_eq_coind (fun s1' s2' => s1' = s1 /\ s2' = s2)).
    intuition. subst s0. subst s3. assumption.
    intuition. subst s0. assumption.
    intuition. subst s3. assumption.
    intuition.
  Qed.
End stream_eq_loop.

Theorem ones_eq''' : stream_eq ones ones'.
  apply stream_eq_loop.
  intuition. intuition. intuition.
Qed.

Require Import Arith.

CoFixpoint fact_slow'(n:nat) := Cons (fact n) (fact_slow' (S n)).
Definition fact_slow := fact_slow' 1.

CoFixpoint fact_iter'(cur acc:nat) := Cons acc (fact_iter' (S cur) (acc*cur)).
Definition fact_iter := fact_iter' 2 1.

Eval simpl in approx fact_iter 5.
Eval simpl in approx fact_slow 5.

Lemma fact_def : forall x n,
    fact_iter' x (fact n * S n) = fact_iter' x (fact (S n)).
  simpl. intros. f_equal. ring.
Qed.

Hint Resolve fact_def.

Lemma fact_eq': forall n, stream_eq (fact_iter' (S n) (fact n))(fact_slow' n).
  intro. apply (stream_eq_coind (fun s1 s2 => exists n, s1 = fact_iter' (S n) (fact n)
                                                /\ s2 = fact_slow' n)).
  intros. simpl. crush. crush. eauto. eauto.
Qed.

Theorem fact_eq'' : stream_eq fact_iter fact_slow.
  apply fact_eq'.
Qed.

Section stream_eq_onequant.
  Variables A B : Type.
  Variables f g : A -> stream B.

  Hypothesis Cons_case_hd : forall x, hd (f x) = hd (g x).
  Hypothesis Cons_case_tl : forall x, exists y, tl (f x) = f y /\ tl (g x) = g y.

  Theorem stream_eq_onequant: forall x, stream_eq (f x) (g x).
    intros; apply (stream_eq_coind (fun s1 s2 => exists x, s1 = f x /\ s2 = g x));
      crush; eauto.
  Qed.

  
  