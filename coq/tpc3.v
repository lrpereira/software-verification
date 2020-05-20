Require Import ZArith.
Require Import List.

Set Implicit Arguments.

Definition dec (n : nat) : {p : nat | n = p + 1} + {n = 0}.
  forall n : nat, {p : nat | n = p + 1} + {n = 0}
refine (fun n:nat => match n return {p : nat | n = p + 1} + {n = 0} with
 | 0 => inright _ _
 | S p => inleft _ (exist _ p _)
end
).

Open Scope Z_scope.

(* Inductive Sorted : list Z -> Prop := *)
(*   | sorted0 : Sorted nil *)
(*   | sorted1 : forall z:Z, Sorted (z :: nil) *)
(*   | sorted2 : forall (z1 z2:Z) (l:list Z), *)
(*         z1 <= z2 -> Sorted (z2 :: l) -> Sorted (z1 :: z2 :: l). *)


Fixpoint count (z:Z) (l:list Z) {struct l} : nat :=
  match l with
  | nil => 0%nat     (* %nat to force the interpretation in nat, since have we open Z_scope *)
  | (z' :: l') =>
      match Z.eq_dec z z' with
      | left _ => S (count z l')
      | right _ => count z l'
      end
  end.

Definition Perm (l1 l2:list Z) : Prop := forall z, count z l1 = count z l2.

Lemma Perm_cons : forall a l1 l2, Perm l1 l2 -> Perm (a::l1) (a::l2).
(* FILL IN HERE *) Admitted.

Lemma Perm_cons_cons : forall x y l, Perm (x::y::l) (y::x::l).
(* FILL IN HERE *) Admitted.



(*Lemma strong_length : *)
