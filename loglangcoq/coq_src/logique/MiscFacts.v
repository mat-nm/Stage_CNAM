From Stdlib Require Import List FunInd Arith Setoid.


Open Scope bool_scope.

Function forallb2 {A B} (f:A -> B -> bool) (l:list A) (l':list B) : bool :=
  match l,l' with
    | nil,nil => true
    | a::l , a'::l' => f a a' && forallb2 f l l'
    | _ , _ => false
  end.


Lemma Forall2_forallb2_iff :
  forall {A B} (f:A -> B -> bool) l l',
    forallb2 f l l' = true <-> (Forall2 (fun x y => f x y = true) l l').
Proof.
  intros A B f l.
  induction l;simpl;intros;split;intros.
  - destruct l'.
    + constructor.
    + inversion H.

  - destruct l'.
    + reflexivity.
    + inversion H.

  - destruct l'.
    + inversion H.
    + constructor.
      * apply Bool.andb_true_iff in H.
        destruct H.
        assumption.
      * apply IHl.
        apply Bool.andb_true_iff in H.
        destruct H.
        assumption.

  - destruct l'.
    + inversion H.
    + inversion H;subst.
      rewrite H3;simpl.
      apply IHl.
      assumption.
Qed.

Lemma Forall2_eq_eq_iff: forall A (l1 l2: list A),  Forall2 eq l1 l2 <-> l1 = l2.
Proof.
  intros A l1.
  induction l1;simpl;split.
  - destruct l2.
    + reflexivity.
    + intro abs.
      inversion abs.
  - intros H.
    subst.
    constructor.
  - destruct l2.
    + intros abs.
      inversion abs.
    + intros h.
      inversion h.
      subst a l1 l2.
      destruct (IHl1 l').
      rewrite H0;auto.
  - intros H.
    subst.
    constructor;auto.
    apply IHl1.
    reflexivity.
Qed.




Lemma beq_nat_diff: forall x y, x <> y -> Nat.eqb x y = false.
Proof.
  intros x y H.
  apply Nat.eqb_neq.
  assumption.
Qed.

Lemma beq_nat_diff_rev: forall x y, x <> y -> Nat.eqb y x = false.
Proof.
  intros x y H.
  apply not_eq_sym in H.
  apply beq_nat_diff.
  assumption.
Qed.

Notation ℕ := nat.
(* Devrait être dans la lib standard. *)
Ltac destr_bool :=
  intros; destruct_all bool; simpl in *; trivial; try discriminate.
Lemma implb_prop : forall a b:bool, implb a b = true -> {a = false} + { b = true }.
Proof.
  destr_bool; intuition.
Qed.



Definition eqExt {A} {B} (f g:A -> B) := forall x, f x = g x. 
Definition eqExt2 {A} {B} {C} (f g:A -> B -> C) := forall x y, f x y = g x y. 

Lemma eqExt_refl A B : Reflexive (@eqExt A B).
Proof.
  intro f.
  intro x.
  reflexivity.
Qed.

Lemma eqExt2_refl A B C : Reflexive (@eqExt2 A B C).
Proof.
  intro f.
  intros x y.
  reflexivity.
Qed.


Lemma eqExt_sym A B : Symmetric (@eqExt A B).
Proof.
  intros f g h.
  red in h.
  intro x.
  rewrite h.
  reflexivity.
Qed.

Lemma eqExt2_sym A B C : Symmetric (@eqExt2 A B C).
Proof.
  intros f g h.
  red in h.
  intros x y.
  rewrite h.
  reflexivity.
Qed.

Lemma eqExt_trans A B : Transitive (@eqExt A B).
Proof.
  intros f g h hyp1 hyp2.
  red in hyp1,hyp2.
  intro x.
  rewrite hyp1.
  apply hyp2.
Qed.

Lemma eqExt2_trans A B C : Transitive (@eqExt2 A B C).
Proof.
  intros f g h hyp1 hyp2.
  red in hyp1,hyp2.
  intros x y.
  rewrite hyp1.
  apply hyp2.
Qed.



Lemma not_None_destruct: forall A (x:option A), x <> None <-> exists o, x = Some o.
Proof.
  intros A x.
  destruct x;split;intros.
  - exists a;auto.
  - intro abs; discriminate.
  - elim H;auto.
  - destruct H.
    discriminate H.
Qed.
