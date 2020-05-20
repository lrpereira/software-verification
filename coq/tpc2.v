Require Import List.

Set Implicit Arguments.

Fixpoint sum (l:list nat) {struct l} : nat :=
  match l with
  | nil => 0
  | cons x xs => x + sum xs
  end.

Theorem ex31 : forall l1 l2, sum (l1 ++ l2) = sum l1 + sum l2.
Proof using.
  intros.
  induction l1.
  - simpl. reflexivity.
  - simpl. rewrite IHl1. apply PeanoNat.Nat.add_assoc.
Qed.

Theorem ex32 : forall (A:Type) (l:list A), length (rev l) = length l.
Proof using.
  intros A l.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite app_length. rewrite IHl.
    simpl. apply PeanoNat.Nat.add_comm.
Qed.

Theorem ex33 : forall (A B:Type) (f:A->B) (l1 l2:list A),
    (map f l1)++(map f l2) = map f (l1++l2).
Proof using.
  intros A B f l1 l2.
  induction l1.
  - simpl. reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.

Theorem ex34 : forall (A B:Type) (f:A->B) (l:list A),
    rev (map f l) = map f (rev l).
Proof using.
  intros A B f l.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. rewrite map_app. simpl. reflexivity.
Qed.

Inductive In (A:Type) (y:A) : list A -> Prop :=
| InHead : forall xs:list A, In y (cons y xs)
| InTail : forall (x:A) (xs:list A), In y xs -> In y (cons x xs).

Lemma my_in_inv : forall (A:Type) (a b:A) (l:list A),
    In b (a :: l) -> b=a \/ (In b l).
Proof using.
  intros.
  inversion H.
  - left. reflexivity.
  - right. assumption.
Qed.

Lemma my_in_or_app : forall (A:Type) (l1 l2: list A) (x:A),
    In x l1 \/ In x l2 -> In x (l1 ++ l2).
Proof using.
  intros A l1 l2 x H.
  destruct H.
  - induction H.
    + simpl. constructor.
    + simpl. constructor. assumption.
  - induction l1.
    + simpl. assumption.
    + rewrite <- app_comm_cons. constructor. assumption.
Qed.

Theorem ex41 : forall (A:Type) (x:A) (l:list A), In x l -> In x (rev l).
Proof using.
  intros A x l H.
  induction H.
  - simpl. apply my_in_or_app. right. apply InHead.
  - simpl. apply my_in_or_app. left. assumption.
Qed.

Theorem ex42 : forall (A B:Type) (y:B) (f:A->B) (l:list A),
    In y (map f l) -> exists x, In x l /\ y = f x.
Proof using.
  intros A B y f l H.
  induction l.
  - simpl in H. inversion H.
  - simpl in H. inversion H.
    * exists a. split.
      -- constructor.
      -- reflexivity.
    * apply IHl in H1.
      destruct H1.
      exists x0. destruct H1. split.
      -- constructor. assumption.
      -- assumption.
Qed.

Theorem ex43 : forall (A:Type) (x:A) (l : list A), In x l -> exists l1, exists l2, l = l1 ++ (x::l2).
Proof using.
  intros A x l H.
  induction H.
  - exists nil. exists xs. reflexivity.
  - destruct IHIn.
    destruct H0.
    rewrite H0.
    exists (x0::x1). exists x2.
    reflexivity.
Qed.

Inductive Prefix (A:Type) : list A -> list A -> Prop :=
| PreNil : forall l:list A, Prefix nil l
| PreCons : forall (x:A) (l1 l2:list A), Prefix l1 l2 -> Prefix (x::l1) (x::l2).

Theorem ex51 : forall (A:Type) (l1 l2:list A), Prefix l1 l2 -> length l1 <= length l2.
Proof using.
  intros.
  induction H.
  - firstorder.
  - elim H.
    + intros. simpl. firstorder.
    + intros. simpl. firstorder.
Qed.

Theorem ex52 : forall l1 l2, Prefix l1 l2 -> (sum l1 <= sum l2).
Proof using.
  intros l1 l2 H.
  induction H.
  - simpl. firstorder.
  - simpl. firstorder.
Qed.

Theorem ex53 : forall (A:Type) (l1 l2:list A) (x:A),
    (In x l1) /\ (Prefix l1 l2) -> In x l2.
Proof using.
  intros A l1 l2 x H.
  destruct H.
  induction H0.
  - induction l.
    + assumption.
    + apply InTail. assumption.
  - inversion H.
    + apply InHead.
    + apply InTail. apply IHPrefix. assumption.
Qed.

Inductive SubList (A:Type) : list A -> list A -> Prop :=
| SLnil : forall l:list A, SubList nil l
| SLcons1 : forall (x:A) (l1 l2:list A), SubList l1 l2 -> SubList (x::l1) (x::l2)
| SLcons2 : forall (x:A) (l1 l2:list A), SubList l1 l2 -> SubList l1 (x::l2).

Theorem ex61 : forall (A:Type)(l1 l2 l3 l4:list A),
    SubList l1 l2 -> SubList l3 l4 -> SubList (l1++l3) (l2++l4).
Proof using.
  intros A l1 l2 l3 l4 H H0.
  induction H.
  - induction l.
    + induction l3.
      * apply SLnil.
      * simpl. assumption.
    + simpl. simpl in IHl. constructor. assumption.
  - simpl. apply SLcons1. assumption.
  - simpl. constructor. assumption.
Qed.

Theorem ex62 : forall (A:Type) (l1 l2:list A),
    SubList l1 l2 -> SubList (rev l1) (rev l2).
Proof using.
  intros A l1 l2 H.
  induction H.
  - simpl. apply SLnil.
  - simpl. apply ex61.
    + apply IHSubList.
    + apply SLcons1. apply SLnil.
  - simpl.
    cut (SubList (rev l1 ++ nil) (rev l2 ++ x :: nil)).
    + rewrite app_nil_r. trivial.
    + apply ex61.
      * assumption.
      * apply SLnil.
Qed.

Theorem ex63 : forall (A:Type) (x:A) (l1 l2:list A),
    Prefix l1 l2 ->  SubList l1 l2.
Proof using.
  intros.
  induction H.
  apply SLnil.
  apply SLcons1.
  apply IHPrefix.
Qed.

Theorem ex64 : forall (A:Type) (x:A) (l1 l2:list A),
    SubList l1 l2 -> In x l1 -> In x l2.
Proof using.
  intros A x l1 l2 H.
  induction H.
  - intro. induction l.
    + assumption.
    + apply InTail. assumption.
  - intro. inversion H0.
    + apply InHead.
    + apply InTail. apply IHSubList. assumption.
  - intro. apply InTail. apply IHSubList. assumption.
Qed.
