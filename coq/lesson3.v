(* ================================================================== *)
(* ==================== Programming and proving ===================== *)
(* ================================================================== *)

Require Import ZArith.
Require Import List.

Set Implicit Arguments.

Fixpoint elem (a:Z) (l:list Z) {struct l} : bool :=   (* !!!!!!!!!!! *)
    match l with
      | nil => false
      | cons x xs => if Z.eq_dec x a then true else (elem a xs)
    end.

Proposition elem_corr : forall (a:Z) (l1 l2:list Z),
                  elem a (app l1 l2) = orb (elem a l1) (elem a l2).
Proof using.
  induction l1.
  - intros. simpl. reflexivity.
  - intros. simpl.
    elim (Z.eq_dec a0 a).
    +  Search orb.
      rewrite Bool.orb_true_l.
      trivial.
    + auto.
Qed.

(* Exercise: *)
Lemma ex : forall (a:Z) (l1 l2:list Z), elem a (app l1 (cons a l2)) = true.
Proof using.
  intros. rewrite elem_corr.
 Search "orb".
  apply Bool.orb_true_iff. right. simpl.
  elim (Z.eq_dec a a); auto.
Qed.

(* ================================================================== *)
(* ======================== Partiality ============================== *)

(* defining the function head *)

Definition head (A:Type) (l:list A) : l<>nil -> A.
(* "refine term" tactic applies to any goal. It behaves like exact with
a big difference: the user can leave some holes (denoted by _ or (_:type))
in the term.
refine will generate as many subgoals as there are holes in the term. *)
  refine (
  match l as l' return l'<>nil -> A with
  | nil => fun H => _
  | cons x xs => fun H => x
  end ).
  elimtype False.  (* cut False. intro H1. elim H1. clear H. *)
  apply H; reflexivity.  (* elim H. reflexivity. *)
Defined.

Print  head.
Print Implicit head.


(* head precondition *)
Definition headPre (A:Type) (l:list A) : Prop := l<>nil.

(* the specification of head *)
Inductive headRel (A:Type) (x:A) : list A -> Prop :=
  headIntro : forall l, headRel x (cons x l).

Print Implicit headRel.


(* we can prove the correctness of head w.r.t. its specification *)
Lemma head_correct : forall (A:Type) (l:list A) (p:headPre l), headRel (head  p) l.
Proof using.
  destruct l.
  - intro H; elim H; reflexivity.
  - intros;  destruct l; [simpl; constructor | simpl; constructor].
    (* change de proof script so that you can see effect each tactic *)
Qed.


Print head.
Check head.


(* ================================================================== *)
(* ==================== Program Extraction ========================== *)

Require Extraction.  (* the extraction framework must be loaded explicitly *)


(* we can convert to Haskell the function head defined *)
Extraction Language Haskell.

Extraction head.

Extraction False_rect.
Extraction Inline False_rect.  (* will make the code more readable *)
Extraction head.

Recursive Extraction head.
Extraction "exemplo1" head.

Extract Inductive list => "[]" [ "[]" "(:)" ].

Recursive Extraction head.
Extraction "exemplo2" head.

(* We have just followed the "weak specification" approach:
   we defined the function and add, as a companion lemma, that the function
   satisfies its specification.
*)


(* ================================================================== *)

(* Instead of this approach, we can give a "strong specification" of a
   function  (using specification types), and extract the function from
   its proof (the prove that the specification is inhabited).
*)

(* An inductive relation "x is the last element of list l" *)
Inductive Last (A:Type) (x:A) : list A -> Prop :=
| last_base : Last x (cons x nil)
| last_step : forall l y, Last x l -> Last x (cons y l).


Theorem last_correct : forall (A:Type) (l:list A), l<>nil -> { x:A | Last x l }.
Proof using.
  induction l.
  - intro H. elim H. reflexivity.
  - intros. destruct l.
    + exists a. constructor.
    + elim IHl.
      * intros. exists x. constructor. assumption.
      * discriminate.
Qed.



Recursive Extraction last_correct.

Extraction Inline False_rect.
Extraction Inline sig_rect.
Extraction Inline list_rect.

Recursive Extraction last_correct.



(* ================================================================== *)

(* Following this alternative approach we can give a "strong specification" of
   function head (using specification types), and extract the function from
   its proof (the prove that the specification is inhabited).
*)

(* Exercise: built an alternative definition of function head called “head corr”
   based on the strong specification mechanism *)

(* Lemma head_correct_v2 : forall (A:Type) (l:list A), l<>nil -> {x:A | head (x::l) = x}. *)




(* ================================================================== *)
(* ======================= Sorting a list =========================== *)

Open Scope Z_scope.

Inductive Sorted : list Z -> Prop :=
  | sorted0 : Sorted nil
  | sorted1 : forall z:Z, Sorted (z :: nil)
  | sorted2 : forall (z1 z2:Z) (l:list Z),
        z1 <= z2 -> Sorted (z2 :: l) -> Sorted (z1 :: z2 :: l).


Fixpoint count (z:Z) (l:list Z) {struct l} : nat :=
  match l with
  | nil => 0%nat     (* %nat to force the interpretation in nat, since have we open Z_scope *)
  | (z' :: l') =>
      match Z.eq_dec z z' with
      | left _ => S (count z l')
      | right _ => count z l'
      end
  end.


Definition Perm (l1 l2:list Z) : Prop :=
                                 forall z, count z l1 = count z l2.


(*
 Exercise: prove that Perm is an equivalence relation (i.e. is reflexive, symmetric and transitive)
*)

Lemma Perm_reflex : forall l:list Z, Perm l l.
Proof using.
  intros.
  unfold Perm.
  intros z.
  reflexivity.
Qed.

Lemma Perm_sym : forall l1 l2, Perm l1 l2 -> Perm l2 l1.
Proof using.
  unfold Perm.
  intros.
  symmetry.
  generalize z.
  assumption.
Qed.


Lemma Perm_trans : forall l1 l2 l3, Perm l1 l2 -> Perm l2 l3 -> Perm l1 l3.
Proof using.
  intros l1 l2 l3 H H0.
  unfold Perm. unfold Perm in H. unfold Perm in H0.
  intro.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

(*  Exercise: prove the following lemmas: *)

Lemma Perm_cons : forall a l1 l2, Perm l1 l2 -> Perm (a::l1) (a::l2).
Proof using.
  unfold Perm.
  intros.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma Perm_cons_cons : forall x y l, Perm (x::y::l) (y::x::l).
Proof using.
  unfold Perm.
  intros x y l z.
  simpl. elim Z.eq_dec.
  - elim Z.eq_dec.
    + intros. reflexivity.
    + intros. reflexivity.
  - intros. elim Z.eq_dec.
    + intros. reflexivity.
    + intros. reflexivity.
Qed.

Fixpoint insert (x:Z) (l:list Z) {struct l} : list Z :=
  match l with
    nil => cons x (@nil Z)
  | cons h t =>
        match Z_lt_ge_dec x h with
          left _ => cons x (cons h t)
        | right _ => cons h (insert x t)
        end
  end.

Fixpoint isort (l:list Z) : list Z :=
  match l with
    nil => nil
  | cons h t => insert h (isort t)
  end.

Print isort.


(* some  usefull lemmas about count *)

Lemma count_insert_eq : forall x l,
                       count x (insert x l) = S (count x l).
Proof using.
  induction l.
  - simpl. destruct (Z.eq_dec x x).
    + reflexivity.
    + destruct n. reflexivity.
  - simpl insert. destruct (Z_lt_ge_dec x a).
    + simpl. destruct (Z.eq_dec x x).
      * reflexivity.
      * easy.
    + simpl. destruct (Z.eq_dec x a).
      * rewrite IHl. reflexivity.
      * assumption.
Qed.

Lemma count_cons_diff : forall z x l, z <> x -> count z l = count z  (x :: l).
Proof using.
  intros. induction l.
  - simpl. destruct (Z.eq_dec z x); easy.
  - simpl. destruct (Z.eq_dec z a).
    + destruct (Z.eq_dec z x); easy.
    + destruct (Z.eq_dec z x); easy.
Qed.


Lemma count_insert_diff : forall z x l, z <> x -> count z l = count z (insert x l).
Proof using.
  intros. induction l.
  - simpl. destruct (Z.eq_dec z x); easy.
  - simpl insert. destruct (Z_lt_ge_dec x a).
    + simpl. destruct (Z.eq_dec z x); try easy.
    + simpl. destruct (Z.eq_dec z a); try easy.
      apply f_equal. apply IHl.
Qed.



(* the two auxiliary lemmas *)

Lemma insert_Perm : forall x l, Perm (x::l) (insert x l).
Proof using.
  unfold Perm; induction l.
 - simpl. reflexivity.
 - simpl insert. destruct (Z_lt_ge_dec x a).
   + reflexivity.
   + intros. rewrite Perm_cons_cons.
     destruct (Z.eq_dec z a).
     * simpl. destruct (Z.eq_dec z a).
       -- destruct (Z.eq_dec z x).
          ++ apply f_equal. rewrite e1. rewrite count_insert_eq. reflexivity.
          ++ apply f_equal. apply count_insert_diff. assumption.
       -- destruct (Z.eq_dec z x).
          ++ destruct n. assumption.
          ++ destruct n. assumption.
     * simpl. destruct (Z.eq_dec z a).
       -- destruct (Z.eq_dec z x); easy.
       -- destruct (Z.eq_dec z x).
          ++ rewrite e. rewrite count_insert_eq. reflexivity.
          ++ rewrite <- count_insert_diff; [reflexivity|assumption].
Qed.



Lemma insert_Sorted : forall x l, Sorted l -> Sorted (insert x l).
Proof using.
  - intros x l H; elim H; simpl.
    + constructor.
    + intro z; elim (Z_lt_ge_dec x z); intros.
      * constructor.
        auto with zarith. constructor.
      * constructor.
        -- auto with zarith.
        -- constructor.
    + intros z1 z2 l0 H0 H1.
      elim (Z_lt_ge_dec x z2); elim (Z_lt_ge_dec x z1).
      * intros. constructor.
        -- omega. (* auto with zarith.*)
        -- constructor.
           ++ omega.
           ++ assumption.
      * intros. constructor.
        -- omega.
        -- assumption.
      * intros. constructor.
        -- omega.
        -- constructor; [omega|assumption].
      * intros. constructor; [omega|assumption].
Qed.


(* the proof that isort is correct *)
Theorem isort_correct : forall (l l':list Z), l'=isort l -> Perm l l' /\ Sorted l'.
Proof using.
  induction l; intros.
  - unfold Perm; rewrite H; split; auto. simpl. constructor.
  - simpl in H.
    rewrite H. (* ??????????? *)
    elim (IHl (isort l)); intros; split.
    + apply Perm_trans with (a::isort l).
      * unfold Perm. intro z. simpl. elim (Z.eq_dec z a).
        -- intros. elim H0; reflexivity.   (* auto with zarith. *)
        -- auto with zarith.   (* intros. elim H0. reflexivity. *)
      * apply insert_Perm.
    + apply insert_Sorted. assumption.
Qed.


(* EXTRACTION *)
(* using specification types *)
Definition inssort : forall (l:list Z), { l' | Perm l l' & Sorted l' }.
Proof using.
  induction l.
  - exists nil. constructor. constructor.
  - elim IHl. intros. exists (insert a x).
(* FILL IN HERE *)
    + apply Perm_trans with (a::x).
      * apply Perm_cons. assumption.
      * apply insert_Perm.
    + apply insert_Sorted. assumption.
Defined.

Extraction Language Haskell.
Recursive Extraction inssort.

Extraction Inline list_rec.
Extraction Inline list_rect.
Extraction Inline sig2_rec.
Extraction Inline sig2_rect.

Extraction inssort.
Recursive Extraction inssort.


(* ================================================================== *)
(* =================== Non-structural recursion ===================== *)

Close Scope Z_scope.

Require Import Recdef. (* because of Function *)


Function div (p:nat*nat) {measure fst} : nat*nat :=
  match p with
  | (_,0) => (0,0)
  | (a,b) => if le_lt_dec b a
             then let (x,y):=div (a-b,b) in (1+x,y)
             else (0,a)
  end.
Proof using.
 intros. simpl. omega.
Qed.



(* Exercise: *)
Function merge (p:list Z*list Z)
{measure (fun p=>(length (fst p))+(length (snd p)))} : list Z :=
  match p with
  | (nil,l) => l
  | (l,nil) => l
  | (x::xs,y::ys) => if Z_lt_ge_dec x y
                     then x::(merge (xs,y::ys))
                     else y::(merge (x::xs,ys))
  end.
(* FILL IN HERE *)
Admitted.


(* ========== Euclidean division correction =========== *)

Definition divRel (args:nat*nat) (res:nat*nat) : Prop :=
          let (n,d):=args in let (q,r):=res in q*d+r=n /\ r<d.

Definition divPre (args:nat*nat) : Prop := (snd args)<>0.


Theorem div_correct : forall (p:nat*nat),  divPre p -> divRel p (div p).
Proof using.
  unfold divPre, divRel.
  intro p.
  (* we make use of the specialised induction principle to conduct the proof... *)
  functional induction (div p); simpl.
  - intro H; elim H; reflexivity.
  - (* a first trick: we expand (div (a-b,b)) in order to get rid of the let (q,r)=... *)
    replace (div (a-b,b)) with (fst (div (a-b,b)),snd (div (a-b,b))) in IHp0.
    + simpl in *. intro H; elim (IHp0 H); intros. split.
      * (* again a similar trick: we expand "x" and "y0" in order to use an hypothesis *)
        change (b + (fst (x,y0)) * b + (snd (x,y0)) = a).
        rewrite <- e1. omega.
      * (* and again... *)
        change (snd (x,y0)<b); rewrite <- e1; assumption.
    + symmetry; apply surjective_pairing.
  - auto.
Qed.

(*================== Resolução do TPC ================*)
(*=== Ex 1 ===*)

Lemma Perm_cons_tpc : forall a l1 l2, Perm l1 l2 -> Perm (a::l1) (a::l2).
Proof using.
  unfold Perm.
  intros.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma Perm_cons_cons_tpc : forall x y l, Perm (x::y::l) (y::x::l).
Proof using.
  unfold Perm.
  intros x y l z.
  simpl. elim Z.eq_dec.
  - elim Z.eq_dec.
    + intros. reflexivity.
    + intros. reflexivity.
  - intros. elim Z.eq_dec.
    + intros. reflexivity.
    + intros. reflexivity.
Qed.

(* === Ex 2 ===*)

Theorem merge_correct : forall l1 l2: list Z,
    (Sorted l1 -> Sorted l2 -> Sorted (merge (l1,l2))) /\ Perm (l1++l2) (merge (l1,l2)).
Admitted.

(* === Ex 3 === *)

Lemma length_correct : forall (A:Set) (l:list A), {x:nat | length l = x}.
Proof using.
  intros A l.
  induction l.
  - simpl. exists 0. reflexivity.
  - simpl. elim IHl. intros. exists (S x). rewrite p. reflexivity.
Qed.

Function sum_right (l:list (nat*nat)) :=
  fold_right (fun x y => (snd x) + y) 0 l.

Lemma sum_right_correct : forall l:list (nat*nat), {x:nat | sum_right l = x}.
Proof using.
  intros.
  induction l.
  - exists 0. simpl. reflexivity.
  - simpl. inversion IHl. elim a. intros. exists (b + x). auto.
Qed.

Extraction Language Haskell.
Extraction sum_right_correct.
Extraction Inline prod_rec.
Extraction Inline prod_rect.
Extraction "sum_right" sum_right_correct.
