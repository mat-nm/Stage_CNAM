

(*
  Lemma tableau_Ou : ∀ f₁ f₂, f₁ ∨ f₂ ⊢ Faux → ((f₁ ∨ f₂) ∧ f₁ ⊢ Faux)
                                               /\ ((f₁ ∨ f₂) ∧ f₂ ⊢ Faux).
  Proof.
    intros f₁ f₂ H.
    split.
    - red.
      intros I H0.
      red in H.
      apply H.
      apply and_affaiblissement_conseq with (f₂:=f₁).
      assumption.
    - apply and_affaiblissement_contr.
      assumption.
  Qed.

  Lemma tableau_Ou' : ∀ F f₁ f₂, F ∧ (f₁ ∨ f₂) ⊢ Faux → ((F ∧ (f₁ ∨ f₂)) ∧ f₁ ⊢ Faux)
                                               /\ ((F ∧ (f₁ ∨ f₂)) ∧ f₂ ⊢ Faux).
  Proof.
    intros F f₁ f₂ H.
    split.
    - red.
      intros I H0.
      red in H.
      apply H.
      apply and_affaiblissement_conseq with (f₂:=f₁).
      assumption.
    - apply and_affaiblissement_contr.
      assumption.
  Qed.
*)


(*
  Lemma tableau_Ou'' : ∀ F f₁ f₂, f₁ ∨ f₂ ∨ F ⊢ Faux 
                                  → (f₁ ∧ (f₁ ∨ f₂ ∨ F) ⊢ Faux)
                                    /\ (f₂ ∧ (f₁ ∨ f₂ ∨ F) ⊢ Faux).
  Proof.
    intros F f₁ f₂ H.
    split.
    - red.
      intros I H0.
      red in H.
      apply H.
      apply and_affaiblissement_conseq with (f₂:=f₁).
      setoid_rewrite Et_sym.
      assumption.
    - setoid_rewrite Et_sym.
      apply and_affaiblissement_contr.
      assumption.
  Qed.
*)

(*
  Lemma tableau_Et : ∀ f₁ f₂, f₁ ∧ f₂ ⊢ Faux → ((f₁ ∧ f₂) ∧ f₁) ∧ f₂ ⊢ Faux.
  Proof.
    intros f₁ f₂ H.
    red.
    intros I H0.
    red in H.
    apply H.
    apply and_affaiblissement_conseq with (f₂:=f₁).
    apply and_affaiblissement_conseq with (f₂:=f₂).
    assumption.
  Qed.

  Lemma tableau_Et' : ∀ F f₁ f₂, F ∧ (f₁ ∧ f₂) ⊢ Faux → ((F ∧ (f₁ ∧ f₂)) ∧ f₁) ∧ f₂ ⊢ Faux.
  Proof.
    intros F f₁ f₂ H.
    red.
    intros I H0.
    red in H.
    apply H.
    apply and_affaiblissement_conseq with (f₂:=f₁).
    apply and_affaiblissement_conseq with (f₂:=f₂).
    assumption.
  Qed.

  Lemma tableau_Et'' : ∀ F f₁ f₂, (f₁ ∧ f₂) ∧ F ⊢ Faux → f₁ ∧ f₂ ∧ ((f₁ ∧ f₂) ∧ F) ⊢ Faux.
  Proof.
    intros F f₁ f₂ H.
    setoid_rewrite Et_assoc.
    setoid_rewrite Et_sym at 2.
    setoid_rewrite <- Et_assoc.
    setoid_rewrite Et_sym at 2.
    setoid_rewrite Et_sym.
    setoid_rewrite Et_sym at 3.
    apply tableau_Et'.
    setoid_rewrite Et_sym.
    assumption.
  Qed.
*)

(*
  Require Recdef.

  Fixpoint hauteur (f:formule): ℕ :=
    match f with
      | ⊤ | ⊥ | Var _ => 0
      | ¬ f => S (hauteur f)
      | f∨g | f∧g | f ⇒ g => S (max  (hauteur f) (hauteur g))
    end.
  Require Omega.


  Function reduce' (f:formule) {measure hauteur f} : formule :=
    match f with
      | ⊤ => ⊤
      | ⊥ => ¬ ⊤
      | Var i => Var i
      | ¬ ⊤ => ¬ ⊤
      | ¬ ⊥ => ⊤
      | ¬ (Var i) => ¬ (Var i)
      | ¬ (f₁ ∨ f₂) => (reduce' (¬f₁)) ∧ (reduce' (¬f₂))
      | ¬ (f₁ ∧ f₂) => (reduce' (¬f₁)) ∨ (reduce' (¬f₂))
      | ¬ (f₁ ⇒ f₂) => (reduce' f₁) ∧ (reduce' (¬f₂))
      | ¬¬ f => (reduce' f)
      | f₁ ∨ f₂ => (reduce' f₁) ∨ (reduce' f₂)
      | f₁ ∧ f₂ => ¬ (¬ (reduce' f₁) ∨ ¬ (reduce' f₂))
      | f₁ ⇒ f₂ => ¬ (reduce' f₁) ∨ (reduce' f₂)
    end.
  Proof.
    - intros f f0 f1 teq0 teq. simpl. auto with arith.
    - intros f f0 f₁ f₂ teq0 teq. simpl.
      assert ((hauteur f₂)<=(max (hauteur f₁) (hauteur f₂))).
      + apply Max.le_max_r.
      + omega.
    - intros f f0 f₁ f₂ teq0 teq. simpl.
      assert ((hauteur f₁)<=(max (hauteur f₁) (hauteur f₂))).
      + apply Max.le_max_l.
      + omega.
    - intros f f0 f₁ f₂ teq0 teq. simpl.
      assert ((hauteur f₂)<=(max (hauteur f₁) (hauteur f₂))).
      + apply Max.le_max_r.
      + omega.
    - intros f f0 f₁ f₂ teq0 teq. simpl.
      assert ((hauteur f₁)<=(max (hauteur f₁) (hauteur f₂))).
      + apply Max.le_max_l.
      + omega.
    - intros f f0 f₁ f₂ teq0 teq. simpl.
      assert ((hauteur f₂)<=(max (hauteur f₁) (hauteur f₂))).
      + apply Max.le_max_r.
      + omega.
    - intros f f0 f₁ f₂ teq0 teq. simpl.
      assert ((hauteur f₁)<=(max (hauteur f₁) (hauteur f₂))).
      + apply Max.le_max_l.
      + omega.
    - intros f f₁ f₂ teq. simpl.
      assert ((hauteur f₂)<=(max (hauteur f₁) (hauteur f₂))).
      + apply Max.le_max_r.
      + omega.
    - intros f f₁ f₂ teq. simpl.
      assert ((hauteur f₁)<=(max (hauteur f₁) (hauteur f₂))).
      + apply Max.le_max_l.
      + omega.
    - intros f f₁ f₂ teq. simpl.
      assert ((hauteur f₂)<=(max (hauteur f₁) (hauteur f₂))).
      + apply Max.le_max_r.
      + omega.
    - intros f f₁ f₂ teq. simpl.
      assert ((hauteur f₁)<=(max (hauteur f₁) (hauteur f₂))).
      + apply Max.le_max_l.
      + omega.
    - intros f f₁ f₂ teq. simpl.
      assert ((hauteur f₂)<=(max (hauteur f₁) (hauteur f₂))).
      + apply Max.le_max_r.
      + omega.
    - intros f f₁ f₂ teq. simpl.
      assert ((hauteur f₁)<=(max (hauteur f₁) (hauteur f₂))).
      + apply Max.le_max_l.
      + omega.
  Qed.

  Lemma morgan_Ou : ∀ f₁ f₂, ¬(f₁ ∨ f₂) ≡ (¬f₁ ∧ ¬f₂).
  Proof.
    intros f₁ f₂.
    unfold equiv , consequence, est_modele.
    simpl.
    split;intros.
    - destruct (interp I f₁).
      + discriminate.
      + assumption.
    - destruct (interp I f₁).
      + discriminate.
      + assumption.
  Qed.

  Lemma morgan_Et : ∀ f₁ f₂, ¬(f₁ ∧ f₂) ≡ (¬f₁ ∨ ¬f₂).
  Proof.
    intros f₁ f₂.
    unfold equiv , consequence, est_modele.
    simpl.
    split;intros.
    - destruct (interp I f₁).
      + assumption.
      + reflexivity.
    - destruct (interp I f₁).
      + assumption.
      + reflexivity.
  Qed.

  Lemma equiv_implique : ∀ x y : formule, (x ⇒ y) ≡ (¬x ∨ y).
  Proof.
    intros x y.
    unfold equiv , consequence, est_modele.
    split;intros.
    - rewrite <- eq_implique. assumption.
    - rewrite eq_implique. assumption.
  Qed.

  Lemma equiv_et : ∀ x y: formule, (x ∧ y) ≡ (¬ (¬x ∨ ¬y)).
  Proof.
    intros x y.
    unfold equiv , consequence, est_modele.
    split;intros.
    - rewrite <- eq_et. assumption.
    - rewrite eq_et. assumption.
  Qed.

  Lemma equiv_not : ⊥ ≡ (¬ ⊤).
  Proof.
    unfold equiv , consequence, est_modele.
    split;intros.
    - rewrite <- eq_not. assumption.
    - rewrite eq_not. assumption.
  Qed.

  Lemma equiv_non_non : ∀ f, ¬¬f ≡ f.
  Proof.
    unfold equiv , consequence, est_modele.
    split;intros.
    - simpl in H. destruct (interp I f);auto.
    - simpl. destruct (interp I f);auto.
  Qed.


  Lemma equiv_congr_non : ∀ f g, (f ≡ g) -> ((¬f) ≡ (¬g)).
  Proof.
    intros f g H. rewrite H. reflexivity.
  Qed.


  Lemma reduce_non : ∀ f, reduce' (¬f) ≡ ¬reduce'(f).
  Proof.
    intros f.
    functional induction reduce' f.
    - repeat rewrite reduce'_equation;try reflexivity;try apply equiv_non_non;
 try solve [symmetry;apply equiv_non_non].
    - repeat rewrite reduce'_equation;try reflexivity;try apply equiv_non_non;
      try solve [symmetry;apply equiv_non_non].
    - repeat rewrite reduce'_equation;try reflexivity;try apply equiv_non_non;
      try solve [symmetry;apply equiv_non_non].
    - repeat rewrite reduce'_equation;try reflexivity;try apply equiv_non_non;
      try solve [symmetry;apply equiv_non_non].
    - repeat rewrite reduce'_equation;try reflexivity;try apply equiv_non_non;
      try solve [symmetry;apply equiv_non_non].
    - repeat rewrite reduce'_equation;try reflexivity;try apply equiv_non_non;
      try solve [symmetry;apply equiv_non_non].
    - rewrite reduce'_equation.
      rewrite reduce'_equation.
      rewrite morgan_Et.
      rewrite <- IHf1.
      rewrite <- IHf0.
      rewrite (reduce'_equation (¬¬f₂)).
      rewrite (reduce'_equation (¬¬f₁)).
      reflexivity.
    - rewrite reduce'_equation.
      rewrite reduce'_equation.
      rewrite morgan_Ou.
      rewrite morgan_Ou.
      rewrite equiv_non_non.
      rewrite equiv_non_non.
      rewrite <- IHf1.
      rewrite <- IHf0.
      rewrite (reduce'_equation (¬¬f₂)).
      rewrite (reduce'_equation (¬¬f₁)).
      reflexivity.
    - rewrite reduce'_equation.
      rewrite morgan_Et.
      rewrite reduce'_equation.
      rewrite <- IHf1.
      rewrite (reduce'_equation (¬¬f₂)).
      reflexivity.
    - rewrite reduce'_equation.
      assumption.
    - rewrite reduce'_equation.
      rewrite morgan_Ou.
      rewrite IHf0.
      rewrite IHf1.
      reflexivity.
    - rewrite reduce'_equation.
      rewrite IHf0.
      rewrite IHf1.
      rewrite equiv_non_non.
      reflexivity.
    - rewrite reduce'_equation.
      rewrite IHf1.
      rewrite morgan_Ou.
      rewrite equiv_non_non.
      reflexivity.
  Qed.

  Lemma reduce'_correct: ∀ f:formule, f ≡ (reduce' f).
  Proof.
    induction f.
    - rewrite reduce'_equation. reflexivity.
    - rewrite reduce'_equation.  apply equiv_not.
    - rewrite reduce'_equation. reflexivity.
    - rewrite reduce_non. apply equiv_congr_non. assumption.
    - rewrite reduce'_equation. rewrite <- IHf1, <- IHf2. reflexivity.
    - rewrite reduce'_equation. rewrite equiv_et.
      rewrite <- IHf1, <- IHf2. reflexivity.
    - rewrite reduce'_equation. rewrite equiv_implique.
      rewrite <- IHf1, <- IHf2. reflexivity.
  Qed.


  (* Propriété d'être formé uniquement avec des ¬, ∨ et ⊤ ou Var. *)
  Inductive is_reduced' : formule → Prop :=
    Vrai_is_red': is_reduced' ⊤
  | Var_is_red': ∀ i, is_reduced' (Var i)
  | NonVrai_is_red': is_reduced' (¬ ⊤)
  | NonVar_is_red': ∀ i, is_reduced' (¬ (Var i))
  | Or_is_red': forall f g,is_reduced' f → is_reduced' g → is_reduced' (f ∨ g).

  Lemma reduce'_complete : ∀ f, is_reduced' (reduce' f).
  Proof.
    induction f.
    - rewrite reduce'_equation. apply Vrai_is_red'.
    - rewrite reduce'_equation. apply NonVrai_is_red'.
    - rewrite reduce'_equation. apply Var_is_red'.
    - rewrite reduce'_equation.
      destruct f;try solve [repeat rewrite reduce'_equation;constructor].
      + admit.
      + 

      apply Non_is_red'. assumption.
    - rewrite reduce'_equation. apply Or_is_red.
      + assumption.
      + assumption.
    - rewrite reduce'_equation. apply Non_is_red. apply Or_is_red.
      + apply Non_is_red. assumption.
      + apply Non_is_red. assumption.
    - rewrite reduce'_equation. apply Or_is_red.
      + apply Non_is_red. assumption.
      + assumption.
  Qed.
*)