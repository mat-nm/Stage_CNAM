From Stdlib Require Import Utf8 FunInd OrderedType PeanoNat Lia.
Require Import multiset_spec multiset.

Module N_OT_obsolete <: OrderedType.

  Definition t : Type := nat.

  Definition eq : t -> t -> Prop := eq.
  Definition lt : t -> t -> Prop := lt.

  Definition eq_refl : forall x : t, eq x x := @eq_refl _.
  Definition eq_sym : forall x y : t, eq x y -> eq y x := @eq_sym _.
  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z := @eq_trans _.

  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z := Nat.lt_trans.
  Definition lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros x y H. unfold lt,eq  in *; lia.
  Defined.

  Functional Scheme nat_compare_rect := Induction for Nat.compare Sort Type.
  
  Definition nat_compare_eq : ∀ n m : nat, Nat.compare n m = Eq → n = m.
  Proof.
    intros n m.
    functional induction (Nat.compare n m) using nat_compare_rect.
    intros _;reflexivity.
    intros abs;discriminate.
    intros abs;discriminate.
    intros H;rewrite (IHc H);reflexivity.
  Defined.


  Definition nat_compare_Lt_lt : forall n m, Nat.compare n m = Lt -> n<m.
  Proof.
    intros n m.
    functional induction (Nat.compare n m) using nat_compare_rect.
    intros abs;discriminate.
    intros;lia.
    intros abs;discriminate.
    intros H;assert (U:=IHc H).
    clear IHc H.
    intros;lia.
  Defined.

  Lemma nat_compare_Gt_gt : forall n m, Nat.compare n m = Gt -> n>m.
  Proof.
    intros n m.
    functional induction (Nat.compare n m) using nat_compare_rect.
    intros abs;discriminate.
    intros abs;discriminate.
    intros;lia.
    intros H;assert (U:=IHc H).
    clear IHc H.
    intros;lia.
  Defined.

  Lemma compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros x y; destruct (Nat.compare x y) as [ | | ] eqn:?.
    apply EQ. apply nat_compare_eq; assumption.
    apply LT. apply nat_compare_Lt_lt; assumption.
    apply GT. apply nat_compare_Gt_gt; assumption.
  Defined.

  (* Hint Immediate eq_sym. *)
  (* Hint Resolve eq_refl eq_trans lt_not_eq lt_trans. *)

  Definition eq_dec : forall x y, { eq x y } + { ~ eq x y }.
  Proof.
    unfold eq,t.
    fix a 1; intros [ | x] [ | y].
    left;reflexivity.
    right;intro abs;discriminate abs.
    right;intro abs;discriminate abs.
    case (Nat.eq_dec x y);intros Heq.
    left;rewrite Heq;reflexivity.
    right;intros abs;elim Heq;injection abs;intros;assumption.
  Defined.



End N_OT_obsolete.
