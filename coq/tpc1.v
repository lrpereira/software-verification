Section P2.

Variable A B C:Prop.

(* Propriedade associativa da disjunção *)
Lemma ex21 : (A \/ B) \/ C -> A \/ (B \/ C).
Proof.
  tauto.
Qed.

Lemma ex22 : (B -> C) -> (A \/ B) -> (A \/ C).
Proof.
  tauto.
Qed.

(* Propriedade associativa da interseção *)
Lemma ex23 : (A /\ B) /\ C -> A /\ (B /\ C).
Proof.
  tauto.
Qed.

(* Propriedade distributiva da disjunção *)
Lemma ex24 : A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).
Proof.
  tauto.
Qed.

(* Propriedade distributiva da interseção *)
Lemma ex25 : (A /\ B) \/ (A /\ C) <-> A /\ (B \/ C).
Proof.
  tauto.
Qed.

(* ex24 ? *)
Lemma ex26 : (A \/ B) /\ (A \/ C) <-> A \/ (B /\ C).
Proof.
  tauto.
Qed.

End P2.

Section P3.

Variable A: Set.  
Variable P Q: A -> Prop.

Lemma ex31 : (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
  intros.
  split.
  - destruct H.
    exists x.
    destruct H.
    assumption.
  - destruct H.
    exists x.
    destruct H.
    assumption.
Qed.

Variable G: A -> A -> Prop.

Lemma ex32 : (exists x, forall y, G x y) -> forall y, exists x, G x y.
Proof.
  intros.
  destruct H.
  exists x.
  apply H.
Qed.

Lemma ex33 : (exists x, P x) -> (forall x, forall y , P x -> Q y) -> forall y, Q y.
Proof.
  intros.
  elim H.
  intro.
  apply H0.
Qed.

Variable R: A->Prop.

Lemma ex34 : forall x, (Q x -> R x) -> exists x, (P x /\ Q x) -> exists x, P x /\ R x.
Proof.
  intros.
  exists x.
  intro.
  exists x.
  split.
  - destruct H0. assumption.
  - apply H. destruct H0. assumption.
Qed.

Lemma ex35 : forall x, (P x -> Q x) -> exists x, (P x ) -> exists y, Q y.
Proof.
  intros.
  exists x.
  intro.
  exists x.
  apply H.
  assumption.
Qed.

Lemma ex36 : (exists x,(P x) \/ exists x, (Q x)) <-> exists x, (P x \/ Q x).
Proof.
  red.
  split.
  - intros. destruct H. destruct H.
    + exists x. left. assumption.
    + destruct H. exists x0. right. assumption.
  - intros. destruct H. destruct H.
    + exists x. left. assumption.
    + exists x. right. exists x. apply H.
Qed.

End P3.

Section P4.

Variable A B : Prop.

Axiom EM : forall A : Prop, A \/ ~A.
  
Lemma ex41 :  ((A -> B) -> A) -> A.
Proof.
  intros.
  elim (EM A).
  - intro. assumption.
  - intro. apply H. intro. contradiction.
Qed.
    
  
Lemma ex42 : forall A : Prop, ~ ~ A -> A.
Proof.
  intros.
  unfold not in H.
  elim (EM A0).
  - trivial.
  - contradiction.
Qed.

Variable S : Set.
Variable P : S -> Prop.

Lemma ex43 : (~ forall x : S, P x) -> (exists x : S , ~ P x).
Proof.
  intros.
  destruct EM with (exists x, ~(P x)).
  - assumption.
  - destruct H.
    intros.
    destruct EM with (P x).
    * assumption.
    * destruct H0.
      exists x.
      assumption.
Qed.
