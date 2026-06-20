
(** %\chapter{Déduction naturelle}%
    #<h1 class="libtitle">Déduction naturelle</h1># *)
(** Ce module définit le système de preuve de la déduction naturelle
    pour la logique propositionnelle. Il établit les propriétés
    suivantes de ce système:
- correction vis-à-vis de la sémantique des propriétés
- complétude vis-à-vis de la sémantique des propriétés. Cette preuve
  est directement inspirée de celle Michel Levy dans son polycopié de
  cours "Introduction à la logique" et dans le livre correspondant. *)

(* begin hide *)

From Stdlib Require Import DecidableType Morphisms FunInd Setoid EqNat Wf_nat Arith Lia.
Require Import multiset tables_de_verite logique_generique logique_propositionnelle_avec_variables.
Import logique_propositionnelle_avec_variables.Notations.
Import LogPropVarEnv.ENV.
Import LogPropVarEnv.DEFS.
Import LogPropVar.
Import LogPropVarEnv.
Implicit Types φ ψ φ₁ φ₂ φ₃: formule.
Implicit Types Γ Δ: env.

(* begin hide *)
Reserved Notation "X ⊢ Y" (at level 90).
(* end hide *)

Open Scope formule_scope.
Declare Scope formule_set_scope.
Open Scope formule_set_scope.
(** On redéfinit la notiation ⊧ pour correspondre à la conséquence
    logique entre un _ensemble_ de formule [Γ] et une formule [f].
    Dans les développement précédents f₁ ⊧ f₂ correspondait à la
    conséquence logique entre deux formule. *)
Notation "Γ ⊧ f" := (consequence_set Γ f): formule_set_scope.




(** * Préliminaires *)
(* begin hide *)
(* Compatibilité de l'égalité sur les environnements avec la
   notion de modèle d'un ensemble de formule. Il s'agit d'un
   généralisation de la compatibilité de la notion de modèle d'une
   seule formule. *)

Add Morphism est_modele_set
    with signature (@Logic.eq _) ==> ENV.eq ==> iff as est_modele_set_morphism.
Proof.
  intros y x y0 H.
  unfold est_modele_set. 
  split.
  - intros H0 x0 H1.
    apply H0.
    rewrite H.
    assumption.
  - intros H0 x0 H1.
    apply H0.
    rewrite <- H.
    assumption.
Qed.



Add Morphism consequence_set
    with signature ENV.eq ==> equiv ==> iff as consequence_set_morphism.
Proof.
  intros x y heqenv x0 y0 heqform.
  split.
  - intros hcons.
    unfold consequence_set in *.
    intros I H1.
    apply heqform.
    eapply hcons.
    rewrite heqenv.
    assumption.
  - intros hcons.
    unfold consequence_set in *.
    intros I HI. 
    apply heqform.
    eapply hcons.
    rewrite <- heqenv.
    assumption.
Qed.

(* end hide *)
Lemma not_ex_contradictoire_2: 
  forall Γ,
    ~(exists n, Var n ∈ Γ /\ ((¬Var n) ∈ Γ \/ (Var n⇒⊥) ∈ Γ))
    -> forall n, (Var n) ∈ Γ -> ~((¬Var n) ∈ Γ \/ (Var n⇒⊥) ∈ Γ).
Proof.
  intros Γ H n H0.
  intro abs.
  destruct abs;eauto.
Qed.

Lemma not_ex_contradictoire_3: 
  forall Γ,
    ~(exists n, (Var n) ∈ Γ /\ ((¬Var n) ∈ Γ \/ (Var n⇒⊥) ∈ Γ))
    -> forall n, (¬Var n) ∈ Γ -> ~ (Var n) ∈ Γ.
Proof.
  intros Γ H n H0.
  intro abs.
  apply H.
  eauto.
Qed.

Lemma not_ex_contradictoire_4: 
  forall Γ,
    ~(exists n, (Var n) ∈ Γ /\ ((¬Var n) ∈ Γ \/(Var n⇒⊥) ∈ Γ))
    -> forall n, (Var n ⇒ ⊥) ∈ Γ -> ~(Var n) ∈ Γ.
Proof.
  intros Γ H n H0.
  intro abs.
  apply H;eauto.
Qed.

(** * Déduction naturelle: Définition *)

(** Définition inductive d'une preuve en deduction naturelle *)

Inductive pf :  env ->formule -> Prop :=
  ax : forall Γ φ, φ ∈ Γ -> Γ ⊢ φ
| true_ax : forall Γ, Γ ⊢ ⊤
| impe: forall Γ φ₁ φ₂,    Γ ⊢ φ₁ ⇒ φ₂ -> Γ ⊢ φ₁ -> Γ ⊢ φ₂
| impi: forall Γ φ₁ φ₂,             φ₁ :: Γ ⊢ φ₂ -> Γ ⊢ φ₁ ⇒ φ₂
| andi: forall Γ φ₁ φ₂,         Γ ⊢ φ₁ -> Γ ⊢ φ₂ -> Γ ⊢ φ₁ ∧ φ₂
| ande1: forall Γ φ₁ φ₂,             Γ ⊢ φ₁ ∧ φ₂ -> Γ ⊢ φ₁
| ande2: forall Γ φ₁ φ₂,             Γ ⊢ φ₁ ∧ φ₂ -> Γ ⊢ φ₂
| noti: forall Γ φ₁,                 φ₁ :: Γ ⊢ ⊥ -> Γ ⊢ ¬ φ₁
| note: forall Γ φ₁ φ₂,       Γ ⊢ φ₁ -> Γ ⊢ ¬ φ₁ -> Γ ⊢ φ₂
| ore: forall Γ φ₁ φ₂ φ₃,
         Γ ⊢ φ₁ ∨ φ₂ -> φ₁::Γ ⊢ φ₃ -> φ₂::Γ ⊢ φ₃ -> Γ ⊢ φ₃
| ori1: forall Γ φ₁ φ₂,                   Γ ⊢ φ₁ -> Γ ⊢ φ₁ ∨ φ₂
| ori2: forall Γ φ₁ φ₂,                   Γ ⊢ φ₂ -> Γ ⊢ φ₁ ∨ φ₂
| fale: forall Γ φ₁,             (¬ φ₁) :: Γ ⊢ ⊥ -> Γ ⊢ φ₁
where " X ⊢ Y" := (pf X Y).

(* begin hide *)
(* A short tactic to check ax. Apply ax and then discharge ENV.mem
    subgoals. *)

Ltac tax_in Γ φ :=
  match Γ with
    | context C [ φ :: _ ] =>
      (* FIXME: this will loop on (φ :: φ :: _) *)
      (repeat rewrite (ENV.add_comm _ φ))
      ; (apply in_add_eq;reflexivity)
  end.

Ltac tax_in_hyp :=
  match goal with
    | h:In ?φ ?Γ |- In ?φ (_ :: ?Γ) => apply in_add;assumption
    | h:In ?φ ?Γ |- In ?φ (_ :: _ :: ?Γ) => (do 2 apply in_add);assumption
  end.

Ltac tax :=
  match goal with
    | |- ?X  ⊢ ?Y => 
      now apply ax; solve [  assumption | tax_in X Y | tax_in_hyp ]
   end.

(* end hide *)
(** ** Exemples de preuve en déduction naturelle

Certaines de ces preuves sont réutilisées plus bas. On utilise une
tactic dédiée pour la règle [ax]: tax. Cette tactique applique [ax]
puis essaie de prouver sa prémisse [p ∈ Γ] automatiquement. *)
Module Exemple_DN.
(* begin show *)
  Lemma ex_DN_1: pf ([X₁]) X₁.
    tax.
  Qed.

  Lemma ex_DN_2: [X₁ , X₂] ⊢ X₁.
    tax.
  Qed.

  Lemma ex_DN_3: [X₂ , X₁] ⊢ X₁.
    tax.
  Qed.

  (** Cette propriété est connue sous le nom « Tiers exclu ». Le tiers
      exclu est prouvable en déduction naturelle pour toute formule [A]. *)

  Lemma a_or_nota : forall A Γ, Γ ⊢ A∨¬A.
  Proof.
    intros A Γ.
    apply fale.
    apply note with (A∨¬A).
    - apply ori2.
      apply noti.
      apply note with (A∨¬A).
      + apply ori1.            
        tax.
      + tax.
    - tax.
  Qed.
(* end show *)
(* begin hide *)
End Exemple_DN.
(* end hide *)


(** * Propriétés remarquables de la déduction naturelles

Ces propriétés sont nécessaires à la preuve de complétude de la
déduction naturelle. *)

(** ** Compatibilité de la preuve avec la notion d'égalité sur les environnements. *)

Lemma equiv_gamma : forall Γ Γ' f, ENV.eq Γ Γ' -> Γ ⊢ f -> Γ' ⊢ f.
Proof.
  intros Γ Γ' f H H0.
  revert Γ' H.
  induction H0;intros.
  - rewrite H0 in H.
    tax.
  - constructor 2.
  - apply impe with φ₁.
    + apply IHpf1.
      assumption.
    + apply IHpf2.
      assumption.
  - apply impi.
    apply IHpf.
    rewrite H.
    reflexivity.
  - apply andi.
    + apply IHpf1.
      assumption.
    + apply IHpf2.
      assumption.
  - apply ande1 with φ₂.
    + apply IHpf.
      assumption.
  - apply ande2 with φ₁.
    + apply IHpf.
      assumption.
  - apply noti.
    + apply IHpf.
      rewrite H.
      reflexivity.
  - apply note with φ₁.
    + apply IHpf1.
      assumption.
    + apply IHpf2.
      assumption.
  - apply ore with φ₁ φ₂.
    + apply IHpf1.
      assumption.
    + apply IHpf2.
      rewrite H.
      reflexivity.
    + apply IHpf3.
      rewrite H.
      reflexivity.
  - apply ori1.
    + apply IHpf.
      assumption.
  - apply ori2.
    + apply IHpf.
      assumption.
  - apply fale.
    + apply IHpf.
      rewrite H.
      reflexivity.
Qed.

(** Le morphisme associé *)

Add Parametric Morphism: pf
    with signature ENV.eq ==> Logic.eq ==> iff as pf_morphism.
Proof.
  intros Γ Γ' heqΓΓ' φ.
  split.
  - intros h.
    eapply equiv_gamma;eauto.
  - intros h.
    eapply equiv_gamma;eauto.
    symmetry.
    assumption.
Qed.

(** ** Règles supplémentaires déductible des règles de base *)

Lemma or_imp: forall B C Γ, ((B ⇒ ⊥) ⇒ C) :: Γ ⊢ (B∨C).
Proof.
  intros  B C Γ.
  apply ore with (φ₁:=B) (φ₂:=¬B).
  - apply Exemple_DN.a_or_nota.
  - apply ori1.
    tax.
  - apply ori2.
    apply impe with (φ₁:=(B ⇒ ⊥)). 
    + tax.      
    + apply impi.
      apply note with (φ₁:=B).
      * tax.
      * tax.
Qed.


Lemma weakening: forall Γ φ ψ, Γ ⊢ ψ -> φ :: Γ ⊢ ψ.
Proof.
  intros Γ φ ψ H.
  revert φ.
  induction H;intros φ'; try now (econstructor; eauto).
  - constructor 1.
    apply in_add.
    assumption.
  - constructor 4. 
    rewrite ENV.add_comm.
    auto.
  - econstructor 8;eauto.
    rewrite ENV.add_comm.
    auto.
  - econstructor 10;eauto.
    + rewrite ENV.add_comm.
      auto.
    + rewrite ENV.add_comm.
      auto.
  - econstructor 13;eauto.
    rewrite ENV.add_comm.
    auto.
Qed.

Lemma weakening_env: forall Γ Δ ψ, Γ ⊢ ψ -> Δ ∪ Γ ⊢ ψ.
Proof.
  intros Γ Δ ψ H.
  induction Δ using multiset_ind.
  - now rewrite <- H0.
  - assumption.
  - rewrite union_rec_left.
    now apply weakening.
Qed.


Lemma contraction: forall Γ Δ φ ψ,
    φ ∈ Γ ->
    Δ == φ :: Γ ->
    Δ  ⊢ ψ ->
    Γ ⊢ ψ.
Proof.
  intros Γ Δ φ ψ HIn HeqΔ Hpf.
  revert Γ φ HIn HeqΔ.
  induction Hpf; intros Γ' **; try now (econstructor; eauto).
  - constructor 1.
    rewrite HeqΔ in *.
    clear HeqΔ.
    destruct (eq_dec φ φ0).
    + now rewrite e.
    + apply -> (in_add_neq φ φ0 Γ');auto.
  - rewrite HeqΔ in *.
    apply impi.
    eapply (IHHpf (φ₁ :: Γ') φ).
    + apply in_add.
      assumption.
    + rewrite HeqΔ in *.
      apply add_comm.
  - rewrite HeqΔ in *.
    apply noti.
    apply (IHHpf (φ₁ :: Γ') φ).
    + now apply in_add.
    + rewrite HeqΔ.
      apply add_comm.
  - rewrite HeqΔ in *.
    apply ore with φ₁ φ₂.
    apply (IHHpf1 Γ' φ).
    + apply HIn.
    + apply HeqΔ.
    + apply (IHHpf2 (φ₁::Γ') φ).
      * now apply in_add.
      * rewrite HeqΔ.
        apply add_comm.
    + apply (IHHpf3 (φ₂::Γ') φ).
      * now apply in_add.
      * rewrite HeqΔ.
        apply add_comm.
  - rewrite HeqΔ in *.
    apply fale.
    apply (IHHpf ((Non φ₁)::Γ') φ).
    + now apply in_add.
    + rewrite HeqΔ.
      apply add_comm.
Qed.
   



Lemma impe_impi_add: forall Γ φ φ' ψ, φ :: Γ ⊢ ψ -> φ' :: Γ ⊢ φ -> φ' :: Γ ⊢ ψ.
Proof.
  intros Γ φ φ' ψ H H0.
  apply impe with (φ₁:=φ).
  - apply impi.
    rewrite ENV.add_comm.
    apply weakening.
    assumption.
  - assumption.
Qed.

Lemma impe_impi: forall Γ φ ψ, φ :: Γ ⊢ ψ -> Γ ⊢ φ -> Γ ⊢ ψ.
Proof.
  intros Γ φ ψ H H0.
  apply impe with (φ₁:=φ).
  - apply impi.  
    assumption.
  - assumption.
Qed.

Lemma impe_impi_add_double: forall Γ φ φ' φ'' ψ,
                              φ :: φ' :: Γ ⊢ ψ ->
                              φ'' :: Γ ⊢ φ ->
                              φ'' :: Γ ⊢ φ' ->
                              φ'' :: Γ ⊢ ψ.
Proof.
  intros Γ φ φ' φ'' ψ H H0 H1.
  apply impe_impi_add with (φ':=φ'') in H.
  - rewrite ENV.add_comm in H.
    apply impe_impi with (φ:=φ').
    + assumption.
    + assumption.
  - rewrite ENV.add_comm.
    apply weakening.
    assumption.
Qed.

Lemma group_and: forall Γ φ φ' ψ,
    φ :: φ' :: Γ ⊢ ψ  ->  (φ ∧ φ') :: Γ ⊢ ψ.
Proof.
  intros Γ φ φ' ψ H.
  apply impe_impi_add_double with (φ:=φ)(φ':=φ')(φ'':=(φ ∧ φ'));auto.
  - apply ande1 with (φ₂:=φ').
    tax.
  - apply ande2 with (φ₁:=φ).
    tax.
Qed.


(** Plusieurs des ces lemmes sont en exercices dans la preuve de M.
    Levy. *)

(** Exercie 46 Levy *)

Lemma and_false_false_or : forall B C Γ, ((B∧C)⇒⊥) :: Γ ⊢ (B⇒⊥)∨(C⇒⊥).
Proof.
  intros B C Γ.
  apply fale.
  apply note with (φ₁:=(B⇒⊥) ∨ (C⇒⊥)).
  - apply ori1.
    apply impi.
    apply note with (φ₁:=(B⇒⊥) ∨ (C⇒⊥)).
    + apply ori2.
      apply impi.
      apply impe with (φ₁:=B∧C).
      * apply weakening.
        apply weakening.
        apply weakening.
        tax.
      * apply andi; tax.
    + tax.
  - tax.
Qed.

Lemma not_not_eq: forall Γ A, Γ ⊢ A -> Γ ⊢ ¬(¬A).
Proof.
  intros Γ A H.
  apply noti.
  apply note with (φ₁:=A). 
  + apply weakening.
    assumption.
  + tax.
Qed.


Lemma not_not_eq'': forall Γ A, (¬(¬A)) :: Γ ⊢ A.
Proof.
  intros Γ A.
  apply fale. 
  apply note with (¬A);try tax.
Qed.

Lemma not_not_eq'''': forall Γ A, ((¬A)⇒⊥) :: Γ ⊢ A.
Proof.
  intros Γ A.
  apply fale. 
  apply impe with (¬A);tax.
Qed.

Lemma and_false_false_or' : forall B C Γ, (¬(B∧C)) :: Γ ⊢ (¬B)∨(¬C).
Proof.
  intros B C Γ.
  apply fale.
  apply note with (φ₁:=(¬B) ∨ (¬C)).
  - apply ori1.
    apply noti.
    apply note with (φ₁:=(¬B) ∨ (¬C)).
    + apply ori2.
      apply noti.
      apply note with (φ₁:=¬(B∧C)).
      * apply weakening.
        apply weakening.
        apply weakening.
        tax.
      * apply not_not_eq.
        apply andi;tax.
    + tax.
  - tax.
Qed.


(** Exo 47, partie 1 *)

Lemma not_or_and_not_1 : forall B C Γ,   (B ∨ C ⇒ ⊥):: Γ ⊢ B⇒⊥.
Proof.
  intros B C Γ.
  apply impi.
  apply impe with (φ₁:=B∨C).
  - tax.
  - apply ori1.
    tax.
Qed.

(** Exo 47, partie 2 *)

Lemma not_or_and_not_2 : forall B C Γ,   (B ∨ C ⇒ ⊥) :: Γ ⊢ C⇒⊥.
Proof.
  intros B C Γ.
  apply impi.
  apply impe with (φ₁:=B∨C).
  - tax.
  - apply ori2.
    tax.
Qed.

(** Exo 47, partie 1, avec le not *)

Lemma not_or_and_not_1' : forall B C Γ,   (¬(B ∨ C)) :: Γ ⊢ ¬B.
Proof.
  intros B C Γ.
  apply noti.
  apply note with (φ₁:=¬(B∨C)).
  - tax.
  - apply not_not_eq.
    apply ori1.
    tax.
Qed.

(** Exo 47, partie 2 *)

Lemma not_or_and_not_2' : forall B C Γ, (¬(B ∨ C)) :: Γ ⊢ ¬C.
Proof.
  intros B C Γ.
  apply noti.
  apply note with (φ₁:=¬(B∨C)).
  - tax.
  - apply not_not_eq.
    apply ori2.
    tax.
Qed.


(** exo 48 Levy (1) *)

Lemma not_imp: forall B C Δ, ((B ⇒ C) ⇒ ⊥) :: Δ ⊢ B.
Proof.
  intros B C Δ.
  apply fale.
  apply impe with (φ₁:=B ⇒ C).
  - tax.
  - apply impi.
    apply note with (φ₁:=B);tax.
Qed.

(** exo 48 Levy (2) *)

Lemma not_imp2: forall B C Δ, ((B ⇒ C) ⇒ ⊥) :: Δ ⊢ C ⇒ ⊥.
Proof.
  intros B C Δ.
  apply impi.
  apply  impe with (φ₁:=B ⇒ C).
  - tax.
  - apply ore with (φ₁:=B) (φ₂:= ¬B).  
    + apply Exemple_DN.a_or_nota.
    + apply impi.
      tax.
     + apply impi.
       apply note with (φ₁:=B);tax.
Qed.

(** exo 48 Levy (1) *)

Lemma not_imp': forall B C Δ, (¬(B ⇒ C)) :: Δ ⊢ B.
Proof.
  intros B C Δ.
  apply fale.
  apply note with (φ₁:=(B ⇒ C)).
  - apply impi.
    apply note with (φ₁:=B);tax.
  - tax.
Qed.


(** exo 48 Levy (2) *)

Lemma not_imp2': forall B C Δ, (¬(B ⇒ C)) :: Δ ⊢ ¬C.
Proof.
  intros B C Δ.
  apply noti.
  apply note with (φ₁:=(B ⇒ C)).
  - apply impi.
    tax.
  - tax.
Qed.

(* Ex 1.13 from Ryan and Huth's book *)
Theorem Ex13 : forall Γ (p q r:formule), ((p ∧ q) ⇒ r) ::Γ ⊢ p ⇒ (q ⇒ r).
Proof.
  intros Γ p q r. 
  apply impi.
  apply impi.
  apply impe with (φ₁:=(p ∧ q)).
  - tax.
  - apply andi;tax.
Qed.

(** * Correction de la déduction naturelle *)


(** Preuve de correction de la déduction naturelle vis-à-vis de la
    sémantique définie dans le chapitre %\og\coqref{logique_propositionnelle_avec_variables}{Logique propositionnelle avec variables}\fg{}%#<a href="logique_propositionnelle_avec_variables.html">Logique propositionnelle avec variables</a>#. *)

Lemma soundness : forall Γ p, Γ ⊢ p -> Γ ⊧ p.
Proof.
  smpl*.
  intros Γ p H I H0.
  induction H;smpl*. (*induction sur la structure de la preuve *)
  (*ax*)
  - intros.
    apply H0.
    assumption.

  - simpl.
    reflexivity.

  (*impe *)
  - intros.
    specialize (IHpf2 H0).
    specialize (IHpf1 H0).
    functional inversion IHpf1;subst;clear IHpf1;auto.
    rewrite IHpf2 in *.
    discriminate.

  (* impi *) 
  - simpl.
    case_eq (interp_def I φ₁).
    + intro.
      rewrite IHpf;auto.
      intro.
      simpl.
      intro h.
      apply ENV.In_destruct_iff in h.
      destruct h.
      * red in H2.
        subst.
        assumption.
      * apply H0.
        assumption.
    + trivial.

  (*eti*)
  - simpl.
    specialize (IHpf2 H0).
    specialize (IHpf1 H0).
    rewrite IHpf2,IHpf1;auto.

  (*ete1 *)
  - simpl in IHpf.
    specialize (IHpf H0).
    functional inversion IHpf;subst;auto.

  (*ete2 *)
  - simpl in IHpf.
    specialize (IHpf H0).
    functional inversion IHpf;subst;auto.

  (* noti *)
  - case_eq (interp_def I φ₁);intros.
    + assert (h:forall f : formule, f ∈ (φ₁ :: Γ) -> ⊧[I] f).
      { intros f h.
        apply ENV.In_destruct_iff in h.
        destruct h;unfold eq in *;subst.
        - assumption.
        - apply H0.
          assumption. }
      specialize (IHpf h).
      inversion IHpf.
    + reflexivity.

  (* note *)
  - specialize (IHpf2 H0).
    specialize (IHpf1 H0).
    functional inversion IHpf2;subst.
    rewrite IHpf1 in *.
    discriminate.

  (* ore *)
  - case_eq (interp_def I φ₁).
    + intros.
      apply IHpf2.
      intro.
      intro h.
      apply ENV.In_destruct_iff in h.
      destruct h.
      * unfold LogPropVar.eq in *.
        subst.
        assumption.
      * apply H0.
        assumption.
    + intros.
      specialize (IHpf1 H0).
      simpl in *.
      functional inversion IHpf1;subst; clear IHpf1.
      * rewrite H3 in H4.
        discriminate.
      * rewrite H3 in H4.
        discriminate.
      * apply IHpf3.
        intro.
        intro h.
        { apply ENV.In_destruct_iff in h.
          destruct h.
          - unfold LogPropVar.eq in * .
            subst.
            symmetry.
            assumption.
          - apply H0.
            assumption. }

  (* ori1 *)
  - simpl.
    specialize (IHpf H0).
    rewrite IHpf.
    destruct (interp_def I φ₂);reflexivity.

  (* ori2 *)
  - simpl.
    specialize (IHpf H0).
    rewrite IHpf.
    destruct (interp_def I φ₁);reflexivity.

  (* False *)
  - case_eq (interp_def I φ₁).
    + trivial.
    + simpl in IHpf.
      intros.
      apply IHpf.
      intro.
      intro h.
      apply ENV.In_destruct_iff in h.
      destruct h.
      * unfold LogPropVar.eq in *.
        subst.
        simpl.
        rewrite H1.
        simpl;trivial.
      * apply H0.
        assumption.
Qed.



(** * Préliminaires de la Preuve de complétude de la déduction naturelle *)

(** ** Mesure sur une formule seule *)

Function mesure (p :formule){struct p}:nat :=
  match p with
      ⊤ => 1
    | ⊥ => 0
    | Var _ =>1
    | ¬ φ₂ => mesure(φ₂)+1
    | φ₂ ⇒ p2 => mesure(φ₂)+mesure(p2)+1
    | φ₂ ∨ p2 => mesure(φ₂)+mesure(p2)+2
    | φ₂ ∧ p2 => mesure(φ₂)+mesure(p2)+1
  end.

(** ** Définition de la mesure sur Γ⊢φ en vue de l'induction *)

(** Fonctino uxiliaire à la suivante. *)

Definition add_mesure := (fun e acc => mesure e + acc).

(** Mesure sur un environnement. On utilisera cette définition sur
    φ::Γ pour définir la mesure sur Γ⊢φ. On additionne les mesures de
    toutes les formules de Γ.*)

Definition gammaMesure (gamma :env):nat :=
  ENV.fold _ add_mesure gamma 0.


(** Definition de la relation d'ordre sur les environnement induite par la mesure. *)

Definition gammaLt (n m:env) := gammaMesure n <  gammaMesure m.

(** Cette relation est bien fondée. *)

Lemma gammaLt_wf : well_founded gammaLt.
apply well_founded_ltof.
Qed.

(** ⊥ est le minimum pour cette mesure. *)

Lemma mesure_not_false : forall C, C <> ⊥ -> mesure C > 0.
Proof.
  destruct C;simpl;intros;try lia.
  elim H.
  reflexivity.
Qed.


(** ** Quelques preuve de compatibilité de la mesure
    en vue de permettre les opérations de remplacement (rewrite,
    symmetry etc)} *)

(** L'ordre des formules dans Γ n'est pas significatif. *)
(* autre formulation: transpose Logic.eq add_mesure *)
Lemma add_mesure_comm:
  forall (k k' : formule) (a : nat),
    add_mesure k (add_mesure k' a) = add_mesure k' (add_mesure k a).
Proof.
  intros k k' a.
  unfold add_mesure.
  lia.
Qed.


Local Add Morphism add_mesure
    with signature Logic.eq ==> Logic.eq ==> Logic.eq as add_mesure_morphism.
Proof.
  intros y y0.
  reflexivity.
Qed.

Local Add Morphism gammaMesure
    with signature ENV.eq ==> Logic.eq as gamma_mesure_morphism.
Proof.
  intros x y H.
  unfold gammaMesure.
  apply ENV.fold_morph;auto.
  - hnf. intros x0 y0 H0. hnf. intros x1 y1 H1.
    unfold LogPropVar.eq in *.
    subst.
    reflexivity.
  - hnf.
    intros k k' a.
    apply add_mesure_comm.
Qed.


Lemma transp_add_mesure : ENV.transpose_neqkey nat Logic.eq add_mesure.
Proof.
  repeat (hnf;intros). unfold add_mesure. lia.  
Qed.


Lemma gammaMesure_congru:
  forall A Γ, gammaMesure (A :: Γ) = add_mesure A (gammaMesure Γ) .
Proof.
  intros A Γ.
  unfold gammaMesure.
  destruct (ENV.multiplicity A Γ) eqn:h;simpl.
  - setoid_rewrite (ENV.multiplicity_fold _ _ _ _ _ transp_add_mesure A _ _ (S n)) at 1;auto.
    + simpl.
      apply f_equal.
      setoid_rewrite (ENV.multiplicity_fold _ _ _ _ _ transp_add_mesure A _ _ n) at 2;auto.
      * apply f_equal2;auto.
        { apply ENV.fold_morphism;auto.
        - apply add_mesure_morphism_Proper.
        - apply transp_add_mesure.
        - rewrite ENV.remove_add.
          reflexivity. }
      * apply ENV.Multiplicity_multiplicity.
        assumption.
    + apply ENV.add_spec_Mult.
      apply ENV.Multiplicity_multiplicity.
      assumption. 
 - setoid_rewrite (@ENV.multiplicity_fold _ _ _ _ _ transp_add_mesure A _ _ 0) at 1 ;auto.
    + simpl.
      apply f_equal.
      apply ENV.fold_morphism;auto.
      { apply add_mesure_morphism_Proper. }
      { apply transp_add_mesure. }
      rewrite ENV.remove_add.
      apply ENV.remove_no_mem.
      apply ENV.multiplicity_none_notin.
      assumption.
    + apply ENV.add_spec_zero_Mult.
      apply ENV.multiplicity_none_notin.
      assumption.
Qed.


(** ** Lemmes auxiliaires sur consequance_set. *)

Lemma conseqset_andl: forall {Γ B C}, Γ ⊧ B∧C -> Γ ⊧ B.
Proof.
  unfold consequence_set,est_modele_set,est_modele in *.
  unfold LogPropVar.interpretation in *.
  simpl.
  intros Γ B C H I H0.
  specialize (H I H0).
  functional inversion H;subst.
  reflexivity.
Qed.

Lemma conseqset_andr: forall {Γ B C}, Γ ⊧ B∧C -> Γ ⊧ C.
Proof.
  unfold consequence_set,est_modele_set,est_modele in *.
  unfold LogPropVar.interpretation in *.
  simpl.
  intros Γ B C H I H0.
  specialize (H I H0).
  functional inversion H;subst.
  reflexivity.
Qed.

Lemma conseqset_impe2: forall {Γ B C}, Γ ⊧ B⇒C -> B :: Γ ⊧ C.
Proof.
  unfold consequence_set,est_modele_set,est_modele in *.
  unfold LogPropVar.interpretation in *.
  simpl.
  intros Γ B C H I H0.
  assert (h:forall f : formule, f ∈ Γ -> ⊧[I] f).
  { intros f H1.
    apply H0.
    apply ENV.in_add.
    assumption. }
  specialize (H I h).
  functional inversion H;subst; clear H.
  - reflexivity.
  - specialize (H0 B).
    rewrite H0 in H1.
    + inversion H1.
    + apply ENV.in_add_eq.
      reflexivity.
Qed.

Lemma conseqset_or_notl: forall {Γ B C}, Γ ⊧ B∨C -> (B⇒⊥) :: Γ ⊧ C.
Proof.
  unfold consequence_set,est_modele_set,est_modele in *.
  unfold LogPropVar.interpretation in *.
  simpl.
  intros Γ B C H I H0.
  assert (h:forall f : formule, f ∈ Γ -> ⊧[I] f).
  { intros f H1.
    apply H0.
    apply ENV.in_add.
    assumption. }
  specialize (H I h).
  functional inversion H;subst; clear H.
  - reflexivity.
  - specialize (H0 (B⇒⊥)).
    assert (h':(B ⇒ ⊥) ∈ ((B ⇒ ⊥) :: Γ)).
    { apply ENV.in_add_eq.
      reflexivity. }
    specialize (H0 h').
    simpl in H0.
    functional inversion H0;subst.
    rewrite <- H1 in H.
    inversion H.
  - reflexivity.
Qed.


Lemma conseqset_lande:
  forall {Γ Γ' B C D},
    Γ' == (B∧C) :: Γ -> Γ' ⊧ D -> (B :: (C :: Γ)) ⊧ D.
Proof.
  unfold consequence_set,est_modele_set,est_modele in *.
  intros Γ Γ' B C D eqEnv H I H1.
  apply H.
  intros f H2.
  rewrite eqEnv in H2.
  assert (⊧[I] B).
  - { apply H1.
    apply ENV.in_add_eq.
    reflexivity. }
  - assert (⊧[I] C).
    + { apply H1.
        rewrite ENV.add_comm.
        apply ENV.in_add_eq.
        reflexivity. }
    + apply ENV.In_destruct_iff in H2.
      destruct H2.
      rewrite H2.
      unfold LogPropVar.interpretation in *.
      simpl.
      unfold table_Et.
      rewrite H0.
      rewrite H3.
      reflexivity.
      apply H1.
      apply   ENV.in_add.
      apply ENV.in_add.
      assumption.
Qed.


Lemma conseqset_neg: forall Γ φ, Γ ⊧ ¬φ -> (φ :: Γ) ⊧ ⊥.
Proof.
  intros Γ φ H.
  red in H.
  red.
  intros I H0.
  absurd (⊧[I]φ).
  - intro.
    unfold est_modele,LogPropVar.interpretation in *.
    simpl in H.
    specialize (H I).
    unfold table_Non in H.
    rewrite H1 in H.
    discriminate H.
    eapply est_model_set_subset;eauto.
  - apply H0.
    apply ENV.in_add_eq.
    reflexivity.
Qed.


Lemma conseqset_or_l:
  forall {Γ Γ' B C D}, Γ' == (B∨C) :: Γ -> Γ' ⊧ D -> B :: Γ ⊧ D.
Proof.
  smpl*.
  intros Γ Γ' B C D eqEnv H I H1.
  apply H.
  intros f H2.
  rewrite eqEnv in H2.
  apply  ENV.In_destruct_iff in H2.
  destruct H2.
  - rewrite H0.
    assert(⊧[I]B).
    { apply H1.
      apply ENV.in_add_eq.
      reflexivity. }
      unfold LogPropVar.interpretation in *.
    smpl*.
    unfold table_Ou.
    rewrite H2.
    case (interp_def I C);reflexivity.
  - apply H1.
    apply ENV.in_add.
    assumption.
Qed.

Lemma conseqset_or_r: 
  forall {Γ Γ' B C D}, Γ' == (B∨C) :: Γ -> Γ' ⊧ D -> C :: Γ ⊧ D.
Proof.
  smpl*.
  intros Γ Γ' B C D eqEnv H I H1.
  apply H.
  intros f H2.
  rewrite eqEnv in H2.
  apply ENV.In_destruct_iff in H2.
  destruct H2.
  - rewrite H0.
    smpl*.
    unfold table_Ou.
    generalize (H1 C).
    case (interp_def I B);case (interp_def I C);intros;try reflexivity.
    apply H2.
    apply ENV.in_add_eq.
    reflexivity.
  - apply H1.
    apply ENV.in_add.
    assumption.
Qed.



(* Same as for or4 *)
Lemma conseqset_imp_l:
  forall {Γ Γ' B C D}, Γ' == (B⇒C) :: Γ -> Γ' ⊧ D -> C :: Γ ⊧ D.
Proof.
  smpl*.
  intros Γ Γ' B C D eqEnv H I H1.
  apply H.
  intros f H2.
  rewrite eqEnv in H2.
  apply  ENV.In_destruct_iff in H2.
  destruct H2.
  - rewrite H0.
    unfold LogPropVar.interpretation in *.
    smpl*.
    unfold table_Implique.
    generalize (H1 C).
    case (interp_def I B);case (interp_def I C);intros;try reflexivity.
    apply H2.
    apply ENV.in_add_eq.
    reflexivity.
  - apply H1.
    apply ENV.in_add.
    assumption.
Qed.

Lemma conseqset_imp_r:
  forall {Γ Γ' B C D}, Γ' == (B⇒C) :: Γ -> Γ' ⊧ D -> (¬B) :: Γ ⊧ D.
Proof.
  smpl*.
  intros Γ Γ' B C D eqEnv H I H1.
  apply H.
  intros f H2.
  rewrite eqEnv in H2.
  apply  ENV.In_destruct_iff in H2.
  destruct H2.
  - rewrite H0.
    smpl*.
    unfold table_Implique.
    generalize (H1 (¬B)).
    unfold LogPropVar.interpretation in *.
    simpl.
    unfold table_Non.
    case (interp_def I B);case (interp_def I C);try reflexivity.
    intro H2.
    apply H2.
    apply ENV.in_add_eq.
    reflexivity.
  - apply H1.
    apply ENV.in_add.
    assumption.
Qed.

Lemma conseqset_notand_l':
  forall {Γ Γ' B C D}, Γ' == (¬(B∧C)) :: Γ -> Γ' ⊧ D -> (¬B) :: Γ ⊧ D.
Proof.
  smpl*.
  intros Γ Γ' B C D eqEnv H I H1.
  apply H.
  intros f H2.
  rewrite eqEnv in H2.
  apply  ENV.In_destruct_iff in H2.
  destruct H2.
  - rewrite H0.
    smpl*.
    unfold table_Non.
    unfold table_Et.
    generalize (H1 (¬B)).
    smpl*.
    unfold table_Non.
    case (interp_def I B);case (interp_def I C);try reflexivity.
    intro H2.
    apply H2.
    apply ENV.in_add_eq.
    reflexivity.
  - apply H1.
    apply ENV.in_add.
    assumption.
Qed.


Lemma conseqset_notand_r':
  forall {Γ Γ' B C D}, Γ' == (¬(B∧C)) :: Γ -> Γ' ⊧ D -> (¬C) :: Γ ⊧ D.
Proof.
  smpl*.
  intros Γ Γ' B C D eqEnv H I H1.
  apply H.
  intros f H2.
  rewrite eqEnv in H2.
  apply  ENV.In_destruct_iff in H2.
  destruct H2.
  - rewrite H0.
    simpl.
    generalize (H1 (¬C)).
    unfold LogPropVar.interpretation in *.
    smpl*.
    unfold table_Non.
    unfold table_Et.
    case (interp_def I B);case (interp_def I C);try reflexivity.
    intro H2.
    apply H2.
    apply ENV.in_add_eq.
    reflexivity.
  - apply H1.
    apply ENV.in_add.
    assumption.
Qed.



Lemma conseqset_notor':
  forall {Γ Γ' B C D}, Γ' == (¬(B∨C)) :: Γ -> Γ' ⊧ D -> (¬B) :: (¬C) :: Γ ⊧ D.
Proof.
  smpl*.
  intros Γ Γ' B C D eqEnv H I H1.
  apply H.
  intros f H2.
  rewrite eqEnv in H2.
  apply  ENV.In_destruct_iff in H2.
  destruct H2.
  - rewrite H0.
    generalize (H1 (¬B)).
    generalize (H1 (¬C)).
    unfold LogPropVar.interpretation in *.
    smpl*.
    unfold table_Non.
    unfold table_Ou.
    case (interp_def I B);case (interp_def I C);try reflexivity;intros H2 H3.
    + apply H3.
      apply ENV.in_add_eq.
      reflexivity.
    + apply H3.
      apply ENV.in_add_eq.
      reflexivity.
    + apply H2.
      rewrite ENV.add_comm.
      apply ENV.in_add_eq.
      reflexivity.
  - apply H1.
    apply ENV.in_add.
    apply ENV.in_add.
    assumption.
Qed.



Lemma conseqset_notimp':
  forall {Γ' B C A}, (¬(B ⇒ C)) :: Γ' ⊧ A -> B :: (¬C) :: Γ' ⊧ A.
Proof.
  smpl*.
  intros  Γ' B C A H I H1.
  apply H.
  intros f H2.
  apply  ENV.In_destruct_iff in H2.
  destruct H2.
  - rewrite H0.
    generalize (H1 (B)).
    generalize (H1 (¬C)).
    unfold LogPropVar.interpretation in *.
    smpl*.
    unfold table_Non.
    unfold table_Implique.
    case (interp_def I B);case (interp_def I C);try reflexivity;intros H2 H3.
    + apply H2.
      rewrite ENV.add_comm.
      apply ENV.in_add_eq.
      reflexivity.
    + apply H3.
      apply ENV.in_add_eq.
      reflexivity.
    + apply H3.
      apply ENV.in_add_eq.
      reflexivity.
  - apply H1.
    apply ENV.in_add.
    apply ENV.in_add.
    assumption.
Qed.


Lemma conseqset_notimp'':
  forall {Γ' B C A}, (¬¬B) :: Γ' ⊧ A ->  B :: (¬C) :: Γ' ⊧ A.
Proof.
  smpl*.
  intros  Γ' B C A H I H1.
  apply H.
  intros f H2.
  apply  ENV.In_destruct_iff in H2.
  destruct H2.
  - rewrite H0.
    generalize (H1 (B)).
    generalize (H1 (¬C)).
    unfold LogPropVar.interpretation in *.
    smpl*.
    unfold table_Non.
    case (interp_def I B);case (interp_def I C);try reflexivity;intros H2 H3.
    + apply H2.
      rewrite ENV.add_comm.
      apply ENV.in_add_eq.
      reflexivity.
    + apply H3.
      apply ENV.in_add_eq.
      reflexivity.
  - apply H1.
    apply ENV.in_add.
    apply ENV.in_add.
    assumption.
Qed.


Lemma conseqset_notimp''':
  forall {Γ' B C A}, ((¬B) ⇒⊥) :: Γ' ⊧ A -> B :: (¬C) :: Γ' ⊧ A.
Proof.
  smpl*.
  intros  Γ' B C A H I H1.
  apply H.
  intros f H2.
  apply  ENV.In_destruct_iff in H2.
  destruct H2.
  - rewrite H0.
    generalize (H1 (B)).
    generalize (H1 (¬C)).
    unfold LogPropVar.interpretation in *.
    smpl*.
    unfold table_Non.
    unfold table_Implique.
    unfold table_Faux.
    case (interp_def I B);case (interp_def I C);try reflexivity;intros H2 H3.
    + apply H2.
      rewrite ENV.add_comm.
      apply ENV.in_add_eq.
      reflexivity.
    + apply H3.
      apply ENV.in_add_eq.
      reflexivity.
  - apply H1.
    apply ENV.in_add.
    apply ENV.in_add.
    assumption.
Qed.


Lemma conseqset_notand_l:
  forall {Γ Γ' B C D}, Γ' == ((B∧C)⇒⊥) :: Γ -> Γ' ⊧ D -> (B ⇒ ⊥) :: Γ ⊧ D.
Proof.
  smpl*.
  intros Γ Γ' B C D eqEnv H I H1.
  apply H.
  intros f H2.
  rewrite eqEnv in H2.
  apply  ENV.In_destruct_iff in H2.
  destruct H2.
  - rewrite H0.
    generalize (H1  (B ⇒ ⊥)).
    unfold LogPropVar.interpretation in *.
    smpl*.
    unfold table_Faux.
    unfold table_Implique.
    unfold table_Et.
    case (interp_def I B);case (interp_def I C);try reflexivity;intros H2.
    apply H2.
    apply ENV.in_add_eq.
    reflexivity.
  - apply H1.
    apply ENV.in_add.
    assumption.
Qed.


Lemma conseqset_notand_r:
  forall {Γ Γ' B C D}, Γ' == ((B∧C)⇒⊥) :: Γ -> Γ' ⊧ D -> (C ⇒ ⊥) :: Γ ⊧ D.
Proof.
  smpl*.
  intros Γ Γ' B C D eqEnv H I H1.
  apply H.
  intros f H2.
  rewrite eqEnv in H2.
  apply  ENV.In_destruct_iff in H2.
  destruct H2.
  - rewrite H0.
    generalize (H1  (C ⇒ ⊥)).
    unfold LogPropVar.interpretation in *.
    smpl*.
    unfold table_Faux.
    unfold table_Implique.
    unfold table_Et.
    case (interp_def I B);case (interp_def I C);try reflexivity;intros H2.
    apply H2.
    apply ENV.in_add_eq.
    reflexivity.
  - apply H1.
    apply ENV.in_add.
    assumption.
Qed.


Lemma conseqset_notor:
  forall {Γ Γ' B C D},
    Γ' == ((B∨C)⇒⊥) :: Γ
    -> Γ' ⊧ D
    -> (B ⇒ ⊥) :: (C ⇒ ⊥) :: Γ ⊧ D.
Proof.
  smpl*.
  intros Γ Γ' B C D eqEnv H I H1.
  apply H.
  intros f H2.
  rewrite eqEnv in H2.
  apply  ENV.In_destruct_iff in H2.
  destruct H2.
  - rewrite H0.
    generalize (H1  (B ⇒ ⊥)).
    generalize (H1  (C ⇒ ⊥)).
    unfold LogPropVar.interpretation in *.
    smpl*.
    unfold table_Faux.
    unfold table_Implique.
    unfold table_Ou.
    case (interp_def I B);case (interp_def I C);try reflexivity;intros H2 H3.
    + apply H3.
      apply ENV.in_add_eq.
      reflexivity.
    + apply H3.
      apply ENV.in_add_eq.
      reflexivity.
    + apply H2.
      rewrite ENV.add_comm.
      apply ENV.in_add_eq.
      reflexivity.
  - apply H1.
    apply ENV.in_add.
    apply ENV.in_add.
    assumption.
Qed.


Lemma conseqset_notimp:
  forall {Γ' B C A}, ((B ⇒ C) ⇒ ⊥) :: Γ' ⊧ A -> B :: (C ⇒ ⊥) :: Γ' ⊧ A.
Proof.
  intros Γ' B C A H0.
  smpl*.
  intros I H1.
  assert (⊧[I] B).
  { apply H1.
    apply ENV.in_add_eq.
    reflexivity. }
  assert (⊧[I] (C⇒⊥)).
  { apply H1.
    rewrite ENV.add_comm.
    apply ENV.in_add_eq.
    reflexivity. }
  assert (interp_def I C=false).
  { smpl*.
    functional inversion H2;subst.
    reflexivity. }
  apply H0.
  intros f H'.
  apply ENV.In_destruct_iff in H'.
  destruct H'.
  - unfold LogPropVar.eq in *.
    subst.
    unfold LogPropVar.interpretation in *.
    smpl*.
    rewrite H.
    rewrite H3.
    reflexivity.
  - apply H1.
    apply ENV.in_add.
    apply ENV.in_add.
    assumption.
Qed.


(** ** Notion de formule atomique, litéral, etc  *)

(** La preuve de complétude de la déduction naturelle fait appel à de
    nombreux cas de base sur les litéraus et formules atomiques. Les
    notions nécessaires sont définies dans cette section. *)

(** Toutes les formes atomiques de formules, sur-ensemble des litéraux
    au sens de Levy. les deux définitions ci-après forment une
    partition de celui-ci. *)

Inductive is_atom: formule -> Prop :=
| Atom_var: forall n, is_atom (Var n)
| Atom_not: forall n, is_atom (¬ (Var n))
| Atom_not2: forall n, is_atom ((Var n) ⇒ ⊥)
| Atom_true: is_atom ⊤
| Atom_not_true: is_atom (¬⊤)
| Atom_not_false: is_atom (¬⊥)
| Atom_false: is_atom ⊥
| Atom_not_false2: is_atom (⊥ ⇒ ⊥)
| Atom_not_true2: is_atom (⊤ ⇒ ⊥).

(** Le sous-ensemble des atomes qui ne sont pas des litéraux au sens
    de Levy. Il s'agit des trois versions atomiques de false. *)

Inductive is_atom_non_literal: formule -> Prop :=
| Atomnl_not_true: is_atom_non_literal (¬⊤)
| Atomnl_false: is_atom_non_literal ⊥
| Atomnl_not_true2: is_atom_non_literal (⊤ ⇒ ⊥).

(** Les littéraux au sens de Levy, un sous ensemble des atomes. *)

Inductive is_literal: formule -> Prop :=
| Literal_var: forall n, is_literal (Var n)
| Literal_not: forall n, is_literal (¬ (Var n))
| Literal_not2: forall n, is_literal ((Var n) ⇒ ⊥)
| Literal_true: is_literal ⊤
| Literal_not_false: is_literal (¬⊥)
| Literal_not_false2: is_literal (⊥ ⇒ ⊥).


Lemma literal_in_atom : forall φ, is_literal φ -> is_atom φ.
Proof.
  intros φ H.
  destruct H;intros;subst;try constructor.
Qed.

(** Les atomes sont soit des [is_literal] soit des [is_atom_non_literal]. *)

Lemma atom_in_literal_ln :
  forall φ,
    is_atom φ -> is_literal φ \/ is_atom_non_literal φ.
Proof.
  intros φ H.
  destruct H;intros;try (now (left ; constructor));try (now (right ; constructor)).
Qed.

#[export] Hint Resolve ENV.Addm_In ENV.Addm_In_other: genenv.

(** la disjonction correspondant aux formules non atomiques. *)

Definition disjunction_non_literal_formula φ :=
  (exists ψ, exists ψ',
              φ = (ψ ∧ ψ')
              \/ φ = (ψ ∨ ψ')
              \/ (φ = (ψ ⇒ ψ') /\ ψ' <> ⊥)
              \/ φ = ((ψ ∧ ψ') ⇒ ⊥)
              \/ φ = ((ψ ∨ ψ') ⇒ ⊥)
              \/ φ = ((ψ ⇒ ψ') ⇒ ⊥)
              \/ φ = (¬(ψ ∧ ψ'))
              \/ φ = (¬(ψ ∨ ψ'))
              \/ φ = (¬(ψ ⇒ ψ')))
  \/ (exists ψ, φ = (¬ (¬ ψ)) \/ φ = ((¬ ψ) ⇒ ⊥)).

(** Preuve que [disjunction_non_literal_formula] contient bien les
    formule non-atomique. *)

Lemma disjunction_non_literal_formula_ok:
  forall φ,
    is_atom φ \/
    disjunction_non_literal_formula φ.
Proof.
  destruct φ; try now (left ; constructor).
  - destruct φ; try now (left ; constructor).
    + right.
      right.
      eauto.
    + right. left. eexists. eexists.
      do 7 right.
      left;eauto.
    + right. left. eexists. eexists.
      do 6 right.
      left;eauto.
    + right. left. eexists. eexists.
      do 8 right.
      eauto.
  - right. left. eexists. eexists.
    right;left;eauto.
  - right. left. eexists. eexists.
    left;eauto.
  - destruct φ2.
    + right. left. eexists. eexists.
    do 2 right; left.
    split;eauto. intro abs;inversion abs.
    + destruct φ1;try now (left;constructor).
      * right. right. eexists. right. eauto.
      * right. left. eexists. eexists.
        do 4 right. left;eauto.
      * right. left. eexists. eexists.
        do 3 right. left;eauto.
      * right. left. eexists. eexists.
        do 5 right. left;eauto.
    + right. left. eexists. eexists.
      do 2 right. left.
      split;eauto. intro abs;inversion abs.
    + right. left. eexists. eexists.
      do 2 right. left.
      split;eauto. intro abs;inversion abs.
    + right. left. eexists. eexists.
      do 2 right. left.
      split;eauto. intro abs;inversion abs.
    + right. left. eexists. eexists.
      do 2 right. left.
      split;eauto. intro abs;inversion abs.
    + right. left. eexists. eexists.
      do 2 right. left.
      split;eauto. intro abs;inversion abs.
Qed.

(** Décision de la propriété [is_literal] *)

Lemma is_literal_dec : forall φ, is_literal φ \/ ~ is_literal φ.
Proof.
  intros φ.
  destruct φ;try (now left; constructor);try (now right;intro abs; inversion abs).
  destruct φ;try (now left; constructor);try (now right;intro abs; inversion abs).
  destruct φ2;try (now left; constructor);try (now right;intro abs; inversion abs).
  destruct φ1;try (now left; constructor);try (now right;intro abs; inversion abs).
Qed.


(** ** Différentes disjonctions sur les termes *)

(** La preuve de complétude de la déduction naturelle fait appel à
    une décomposition par cas sur les termes et sur l'environnement,
    cette section définit plusieurs disjonctions et propriétés
    associées. *)

Definition disjunction_formula φ :=
  (exists ψ, exists ψ', φ = (ψ ∧ ψ') \/ φ = (ψ ⇒ ψ') \/ φ = (ψ ∨ ψ'))
  \/ ((~ is_literal φ) /\ (exists ψ, φ = ¬ ψ))
  \/ is_atom_non_literal φ
  \/ is_literal φ. (* En fait seulement ⊤, x, ¬x ou ¬⊥, virer ¬⊥ des litéraux? *)

Lemma disjunction_formula_ok : forall φ, disjunction_formula φ.
Proof.
  intros φ.
  unfold disjunction_formula.
  destruct φ;eauto 8.
  - repeat right. constructor.
  - do 2 right. left. constructor.
  - repeat right. constructor.
  - right.
    destruct (is_literal_dec (¬φ)).
    + inversion H; subst.
      * repeat right. constructor.
      * repeat right. constructor.
    + left.
      split;eauto.
Qed.




Definition env_disjunction2 Γ :=
  (exists φ, φ ∈ Γ /\ disjunction_non_literal_formula φ)
  \/ (exists φ, φ ∈ Γ /\ is_atom_non_literal φ)
  \/ (forall ψ, ψ ∈ Γ -> is_literal ψ)
  \/ ENV.Empty Γ.



Lemma env_disjunction_stable_add2 :
  forall Γ Γ' n φ, ENV.Add_multiple φ n Γ Γ'
                   -> env_disjunction2 Γ
                   -> env_disjunction2 Γ'.
Proof.
  intros Γ Γ' n φ haddΓΓ' hdisjΓ.
  unfold env_disjunction2 in *.
  decompose [ex or and] hdisjΓ; clear hdisjΓ.
  - assert (x ∈ Γ').
    { eapply ENV.Addm_In_other;eauto. }
    left.
    exists x;auto.
  - right. left.
    eauto with genenv.
  - destruct (disjunction_non_literal_formula_ok φ).
    + destruct (atom_in_literal_ln φ);auto.
      * right. right. left. intros ψ h.
        { destruct (formule_eq_dec φ ψ).
          * subst. assumption.
          * assert (ψ ∈ Γ).
            { eapply ENV.Add_multiple_neq_o;eauto. }
            apply H;auto. }
      * right. left. eauto with genenv.
    + left. exists φ;split;auto.
      eapply ENV.Addm_In;eauto. 
  - destruct (disjunction_non_literal_formula_ok φ).
    + destruct (atom_in_literal_ln φ);auto.
      * do 2 right. left. intros ψ h.
        { destruct (formule_eq_dec φ ψ).
          * subst. assumption.
          * assert (ψ ∈ Γ).
            { eapply ENV.Add_multiple_neq_o;eauto. }
            rewrite (ENV.in_empty_false Γ H ψ) in H2.
            contradiction. }
      * right. left. eauto with genenv.
    + left. exists φ;split;auto.
      eapply ENV.Addm_In;eauto. 
Qed.



(* TODO: have a ForAll in ENV and use it instead of (forall ψ,
   ENV.In ψ Γ -> is_literal ψ). for now we have only
   ENV.Mapsptes.for_all *)
Lemma disjunction_gamma2 :
  forall Γ:env, env_disjunction2 Γ.
Proof.

  intros Γ.
  pattern Γ.
  apply ENV.multiset_Ind; clear Γ.
  - intros.
    repeat right.
    assumption.
  - intros φ n Γ Γ' IH hnotin hadd.
    eapply env_disjunction_stable_add2;eauto.
Qed.



(** Ceci est plus ou moins la disjonction de Levy utilisé dans la
    preuve de complétude. Dans le couple Γ⊢φ, nous avons les cas suivants:
    - Soit φ est une formule composée (∨, ∧, ⇒, négation d'un non litéral)
    - Soit il existe dans Γ une formule composée (légèrement différente: disjunction_non_literal_formula)
    - Soit il existe un litéral faux dans Γ (is_atom_non_literal, trois versions , une seule chez Levy)
    - Γ ne contient que des litéraux et la formule est atomique (litéral ou faux).
*)
Lemma disjunction_gamma_formule :
  forall (Γ:env) (φ:formule),
    (exists ψ ψ', (φ = (ψ ∧ ψ')) \/ (φ = (ψ ⇒ ψ'))\/ (φ = (ψ ∨ ψ')))
    \/ ((~ is_literal φ) /\ (exists ψ, φ = ¬ ψ))
    \/ (exists ψ, ψ ∈ Γ /\ disjunction_non_literal_formula ψ)
    \/ (exists ψ, ψ ∈ Γ /\ is_atom_non_literal ψ)
    \/ ((forall ψ, ψ ∈ Γ -> is_literal ψ) /\ (is_atom_non_literal φ))
    \/ ((forall ψ, ψ ∈Γ -> is_literal ψ) /\ is_literal φ).
Proof.
  intros Γ φ.
  destruct (disjunction_formula_ok φ).
  - left. assumption.
  - right.
    pose (h:=disjunction_gamma2 Γ).
    clearbody h.
    unfold env_disjunction2 in h.
    destruct h as [h|h].
    { do 1 right.
      left. assumption. }
    destruct h.
    { do 2 right. left. eauto. }
    destruct H.
    { left. assumption. }
    destruct H0.
    + destruct H.
      * do 3 right. left;eauto.
      * do 4 right. eauto. 
    + destruct H.
      * do 3 right. left.
        split;auto.
        intros ψ H1.
        absurd (ψ ∈ Γ);auto.
        apply ENV.Empty_no_mem.
        assumption.
      * do 4 right.
        split;auto.
        intros ψ H1.
        absurd (ψ ∈ Γ);auto.
        apply ENV.Empty_no_mem.
        assumption.
Qed.    


      

(** ** Notion d'interprétation caractéristique d'un environnement *)

(** Définition de l'interpétation caractéristique d'un environnement Γ *)

Definition interp_caracteristique (Γ:ENV.t) : nat -> bool := fun n=>ENV.mem (Var n) Γ.
Definition interp_anticaracteristique (Γ:ENV.t) : nat -> bool :=
  fun n=>negb(orb(ENV.mem (¬Var n) Γ) (ENV.mem (Var n⇒ ⊥) Γ)).

Lemma interp_caracteristique_1_new :
  forall Γ,
    (forall ψ, ψ ∈ Γ -> is_literal ψ)
    -> ~(exists n, (Var n)∈ Γ /\ ((¬Var n) ∈ Γ \/ (Var n⇒⊥) ∈ Γ))
    -> est_modele_set (interp_caracteristique Γ) Γ.
Proof.
  intros Γ hall_lit hnot_contradict.
  red.
  intros f hfinΓ.
  red.
  unfold interp_caracteristique.
  assert (hfislit:is_literal f).
  { apply hall_lit.
    assumption. }
  destruct hfislit;unfold LogPropVar.interpretation in *;simpl;try rewrite hfinΓ;auto.
  - apply mem_in_iff.
    assumption.
  - assert (hnnotinΓ: ~ (Var n) ∈ Γ).
    { intro abs.
      apply hnot_contradict.
      exists n.
      split.
      - assumption.
      - left.
        assumption. }
    rewrite ENV.mem_in_iff in hnnotinΓ.
    assert (ENV.mem (Var n) Γ = false).
    { destruct (ENV.mem (Var n) Γ);auto. 
      elim hnnotinΓ;auto. }
    simpl.
    rewrite H.
    reflexivity.
  - unfold table_Implique, table_Faux.
    assert (hnnotinΓ: ~ (Var n) ∈ Γ).
    { intro abs.
      apply hnot_contradict.
      exists n.
      split.
      - assumption.
      - right.
        assumption. }
    rewrite ENV.mem_in_iff in hnnotinΓ.
    assert (ENV.mem (Var n) Γ = false).
    { destruct (ENV.mem (Var n) Γ);auto. 
      elim hnnotinΓ;auto. }
    simpl.
    rewrite H.
    reflexivity.
Qed.


Lemma interp_caracteristique_6_new :
  forall Γ n, ~ (Var n) ∈ Γ -> interpretation (interp_caracteristique Γ) (Var n) false.
Proof.
  intros Γ n H.
  unfold interp_caracteristique.
  apply ENV.not_mem_in_iff in H.
  simpl.
  assumption.
Qed.

Lemma interp_caracteristique_5_new :
  forall Γ n, ~ (Var n) ∈ Γ -> ~est_modele (interp_caracteristique Γ) (Var n).
Proof.
  intros Γ n H.
  red.
  intros H0.
  red in H0.
  unfold LogPropVar.interpretation in *.
  rewrite (interp_caracteristique_6_new) in H0.
  - discriminate.
  - assumption.
Qed.
  
Lemma interp_anticaracteristique_1_new :
  forall Γ,
    (forall ψ, ψ ∈ Γ -> is_literal ψ)
    -> ~(exists n, (Var n) ∈ Γ
                   /\ ((¬Var n) ∈ Γ \/ (Var n⇒⊥) ∈ Γ))
    -> est_modele_set (interp_anticaracteristique Γ) Γ.
Proof.
  intros Γ hall_lit hnot_contradict.
  red.
  intros f hfinΓ.
  red.
  unfold interp_anticaracteristique.
  assert (hfislit:is_literal f).
  { apply hall_lit.
    assumption. }
  destruct hfislit;unfold LogPropVar.interpretation in *; simpl;try auto.
  - assert (~((¬Var n) ∈ Γ \/ (Var n ⇒ ⊥) ∈ Γ)).
    { apply not_ex_contradictoire_2.
      + assumption.
      + assumption. }
    setoid_rewrite ENV.mem_in_iff in H.
    assert (ENV.mem (¬Var n) Γ = false /\ ENV.mem (Var n ⇒ ⊥) Γ = false).
    { destruct (ENV.mem (¬Var n) Γ). 
      - destruct H.
        left;auto.
      - split;auto.
        destruct (ENV.mem (Var n ⇒ ⊥) Γ). 
        + destruct H.
          right;auto.
        + reflexivity. }
    destruct H0 as [h1 h2].
    rewrite h1,h2.
    reflexivity.
  - apply -> (ENV.mem_in_iff  Γ (¬Var n)) in hfinΓ.
    rewrite hfinΓ.
    rewrite Bool.orb_true_l.
    reflexivity.
  - apply -> (ENV.mem_in_iff  Γ (Var n ⇒ ⊥)) in hfinΓ.
    rewrite hfinΓ.
    rewrite Bool.orb_true_r.
    reflexivity.
Qed.



Lemma interp_anticaracteristique_6_new :
  forall Γ n, ~ (¬Var n) ∈ Γ -> ~ (Var n ⇒ ⊥) ∈ Γ
              -> ⊧[interp_anticaracteristique Γ] (Var n).
Proof.
  intros Γ n h h'.
  unfold est_modele,interpretation,interp_anticaracteristique.
  simpl.
  apply ENV.not_mem_in_iff in h.
  apply ENV.not_mem_in_iff in h'.
  simpl.
  rewrite h , h'.
  reflexivity.
Qed.


Lemma interp_anticaracteristique_not_negb: 
  forall Γ k,
  interp_def (interp_anticaracteristique Γ) (¬Var k) =
  negb (interp_def (interp_anticaracteristique Γ) (Var k)).
Proof.
  intros Γ k.
  smpl*.
  reflexivity.
Qed.


(** ** Propriétés des environnements ne contenant que des litéraux *)

Lemma ex_listeral_contradictoire_dec_new: forall Γ,
  (exists n, (Var n) ∈ Γ /\ ((¬Var n) ∈ Γ \/ (Var n⇒⊥) ∈ Γ))
  \/ ~(exists n, (Var n) ∈ Γ /\ ((¬Var n)∈ Γ \/ (Var n⇒⊥) ∈ Γ)).
Proof.
  intros Γ.
  pattern Γ.
  apply ENV.multiset_ind;intros;clear Γ.
  - destruct H0;[left|right];try (progress decompose [ex and or] H0;try clear H0).
    + exists x;intuition;auto;rewrite <- H;auto.
    + exists x;intuition;auto;rewrite <- H;auto.
    + intro abs.
      destruct H0.
      (progress decompose [ex and or] abs;try clear abs;try rewrite <- H in *; eauto). 
  - right.
    intro abs.
    (progress decompose [ex and] abs;try clear abs).
    eapply ENV.empty_in_iff;eauto.
  - destruct H.
    + left.
    decompose [and ex] H; clear H.
    exists x0;auto.
    repeat split;auto.
      * eapply ENV.Add_In_other;eauto.
        apply ENV.Add_of_add.
      * { destruct H2.
          - left.
            eapply ENV.Add_In_other;eauto.
            apply ENV.Add_of_add.
          - right.
            eapply ENV.Add_In_other;eauto.
            apply ENV.Add_of_add. }
    + assert (h: (exists m, (x = Var m) \/ (x = ¬Var m) \/ (x = (Var m ⇒ ⊥)))
              \/ ~(exists m, (x= Var m) \/ (x= ¬Var m) \/ (x = (Var m ⇒ ⊥)))).
      { clear H Γ0.
        destruct x;eauto;try (right;intro abs; decompose [ex or and] abs;discriminate).
        - destruct x;eauto;try (right;intro abs; decompose [ex or and] abs;discriminate).
        - destruct x2;eauto;try (right;intro abs; decompose [ex or and] abs;discriminate).
          destruct x1;eauto;try (right;intro abs; decompose [ex or and] abs;discriminate).
 }
      destruct h.
      * destruct H0.
        { destruct H0.
          - destruct (ENV.In_dec Γ0 (¬(Var x0))).
            + left.
              exists x0.
              split.
              * subst.
                apply ENV.in_add_eq.
                reflexivity.
              * left.
                eapply ENV.Add_In_other;eauto.
                eapply ENV.Add_of_add.
            + destruct (ENV.In_dec Γ0 ((Var x0) ⇒ ⊥)).
              * left.
                subst.
                exists x0.
                { split.
                  - apply ENV.in_add_eq. reflexivity.
                  - right.
                    eapply ENV.Add_In_other;eauto.
                    eapply ENV.Add_of_add. }
              * right.
                subst.
                intro abs.
                { decompose [ex or and] abs;clear abs.
                  - apply ENV.Add_In_other  with (k':=(Var x0)) (m':=Γ0) in H0 ;eauto;auto.
                    + fold ENV.In in *.
                      assert ((Var x) ∈ Γ0).
                      { eapply ENV.in_add_neq;eauto.
                        intros abs.
                        rewrite abs in n;contradiction. }
                      destruct H.
                      exists x;auto.
                  + fold  ENV.In in *.
                    assert ((¬Var x) ∈ Γ0).
                    * eapply ENV.in_add_neq;eauto.
                      intros abs.
                      inversion abs.
                    * rename x0 into y.
                      { destruct (eq_nat_dec y x).
                        - subst.
                          contradiction.
                        - assert ((Var x) ∈ Γ0).
                          { eapply  ENV.in_add_neq;eauto.
                            intro abs.
                            inversion abs.
                            contradiction. }
                          destruct H.
                          exists x;auto. }
                  - apply ENV.Add_In_other  with (k':=(Var x0)) (m':=Γ0) in H0 ;eauto;auto.
                    + fold  ENV.In in *.
                      assert ((Var x) ∈ Γ0).
                      { eapply ENV.in_add_neq;eauto.
                        intros abs.
                        rewrite abs in n0;contradiction. }
                      destruct H.
                      exists x;auto.
                  + fold  ENV.In in *.
                    assert ((Var x ⇒ ⊥) ∈ Γ0).
                    * eapply ENV.in_add_neq;eauto.
                      intros abs.
                      inversion abs.
                    * rename x0 into y.
                      { destruct (eq_nat_dec y x).
                        - subst.
                          contradiction.
                        - assert ((Var x) ∈ Γ0).
                          { eapply  ENV.in_add_neq;eauto.
                            intro abs.
                            inversion abs.
                            contradiction. }
                          destruct H.
                          exists x;auto. }
                }
                
          - destruct (ENV.In_dec Γ0 (Var x0)).
            + left.
              fold  ENV.In in *.
              exists x0.
              split.
              * eapply ENV.Add_In_other;eauto.
                eapply ENV.Add_of_add.
              * { destruct H0;subst.
                  - left.
                    apply ENV.in_add_eq.
                    reflexivity.
                  - right.
                    apply ENV.in_add_eq.
                    reflexivity. }
            + right.
              fold  ENV.In in *.
              intro abs.
              decompose [ex and or] abs;clear abs.
              * { destruct H0;subst.
                  - destruct (eq_nat_dec x0 x1).
                    + subst.
                      assert ((Var x1) ∈ Γ0).
                      { eapply  ENV.in_add_neq;eauto.
                        intro abs.
                        inversion abs. }
                      contradiction.
                    +  assert ((Var x1) ∈ Γ0).
                      { eapply  ENV.in_add_neq;eauto.
                        intro abs.
                        inversion abs. }
                      assert ((¬Var x1) ∈ Γ0).
                      { eapply  ENV.in_add_neq;eauto.
                        intro abs.
                        inversion abs.
                        contradiction. }
                      destruct H.
                      exists x1;auto.
                  - assert ((Var x1) ∈ Γ0).
                    { eapply  ENV.in_add_neq;eauto.
                      intro abs.
                      inversion abs. }
                    assert ((¬Var x1) ∈ Γ0).
                    { eapply  ENV.in_add_neq;eauto.
                      intro abs.
                      inversion abs. }
                    destruct H.
                    exists x1;auto.
                }
              * { destruct H0;subst.
                  - assert ((Var x1) ∈ Γ0).
                    { eapply  ENV.in_add_neq;eauto.
                      intro abs.
                      inversion abs. }
                    assert ((Var x1 ⇒ ⊥) ∈ Γ0).
                    { eapply  ENV.in_add_neq;eauto.
                      intro abs.
                      inversion abs. }
                    destruct H.
                    exists x1;auto.
                  - destruct (eq_nat_dec x0 x1).
                    + subst.
                      assert ((Var x1) ∈ Γ0).
                      { eapply  ENV.in_add_neq;eauto.
                        intro abs.
                        inversion abs. }
                      contradiction.
                    +  assert ((Var x1) ∈ Γ0).
                      { eapply  ENV.in_add_neq;eauto.
                        intro abs.
                        inversion abs. }
                      assert ((Var x1 ⇒ ⊥) ∈ Γ0).
                      { eapply  ENV.in_add_neq;eauto.
                        intro abs.
                        inversion abs.
                        contradiction. }
                      destruct H.
                      exists x1;auto.
                }
        }

      * right.
        intro abs.
        { decompose [ex and or] abs; clear abs.
          - assert ((Var x0) ∈ Γ0).
            { eapply  ENV.in_add_neq; eauto. }
            assert ((¬Var x0) ∈ Γ0).
            { eapply  ENV.in_add_neq; eauto 6. }
            destruct H.
            exists x0;auto.
          - assert ((Var x0) ∈ Γ0).
            { eapply  ENV.in_add_neq; eauto. }
            assert ((Var x0 ⇒ ⊥) ∈ Γ0).
            { eapply  ENV.in_add_neq; eauto 6. }
            destruct H.
            exists x0;auto. }
Qed.

(* TODO: remplacer par is_atom_non_literal *)
Lemma literaux_conseq_false_new:
  forall Γ,
    (forall ψ, ψ ∈ Γ -> is_literal ψ)
    -> Γ ⊧ ⊥
    -> (exists n, (Var n) ∈ Γ /\ ((¬ Var n) ∈ Γ \/ (Var n ⇒⊥) ∈ Γ)).
Proof.
  intros Γ H H0.
  destruct (ex_listeral_contradictoire_dec_new Γ);unfold LogPropVar.interpretation.
  - assumption.
  - exfalso.
    assert (est_modele_set (interp_caracteristique Γ) Γ).
    { apply interp_caracteristique_1_new;auto. }
    assert (⊧[interp_caracteristique Γ] ⊥).
    apply H0.
    assumption.
    red in H3.
    simpl in H3.
    inversion H3.
Qed.
  

Lemma literaux_conseq:
  forall Γ k,
    (forall ψ, ψ ∈ Γ -> is_literal ψ)
    -> Γ ⊧ (Var k)
    -> (exists n, (Var n) ∈ Γ /\ ((¬ Var n) ∈ Γ \/ (Var n⇒ ⊥) ∈ Γ))
       \/ (Var k) ∈ Γ.
Proof.
  intros Γ n H H0.
  destruct (ENV.In_dec Γ (Var n));fold ENV.In in *.
  - right;assumption.
  - left.
    destruct (ex_listeral_contradictoire_dec_new Γ).
    + assumption.
    + assert (est_modele_set (interp_caracteristique Γ) Γ).
      { apply interp_caracteristique_1_new;auto. }
      absurd (est_modele (interp_caracteristique Γ) (Var n)).
      * apply interp_caracteristique_5_new.
        assumption.
      * apply H0. assumption.
Qed.


Lemma literaux_conseq_neg:
  forall Γ k,
    (forall ψ, ψ ∈ Γ -> is_literal ψ)
    -> Γ ⊧ (¬Var k)
    -> (exists n, (Var n) ∈ Γ /\ ((¬ Var n) ∈ Γ \/ (Var n⇒ ⊥) ∈ Γ))
       \/ (¬Var k) ∈ Γ\/ (Var k ⇒ ⊥) ∈ Γ.
Proof.
  intros Γ k H H0.
  destruct (ENV.In_dec Γ (¬Var k));fold ENV.In in *.
  - right;left;assumption. 
  - destruct (ENV.In_dec Γ (Var k ⇒ ⊥));fold ENV.In in *.
    + right. right. assumption.
    + destruct (ex_listeral_contradictoire_dec_new Γ).
      * left;auto.
      * assert (est_modele_set (interp_anticaracteristique Γ) Γ).
        { apply interp_anticaracteristique_1_new;auto. }
        { absurd (est_modele (interp_anticaracteristique Γ) (¬Var k)).
          - unfold est_modele,LogPropVar.interpretation.
            intro abs.
            rewrite interp_anticaracteristique_not_negb in abs.
            rewrite interp_anticaracteristique_6_new in abs;auto;try discriminate.
          - apply H0. assumption. }
Qed.





(** ** Preuve de la complétude de la déduction naturelle *)

Ltac solve_gammalt := 
  try unfold gammaLt;
  repeat rewrite (@gammaMesure_congru);
  try unfold add_mesure;
  simpl;
  auto;
  try lia.

Ltac infer_inv_remove :=
  match goal with
    | H:?φ ∈ ?Γ |- _ =>
      let D := fresh "Δ" in
      remember (ENV.remove φ Γ) as D
      ; let heq := fresh "heq" in
        assert (heq:ENV.eq Γ (φ :: D))
        ; [ try (subst;  symmetry; apply ENV.remove_same_add_in;auto)
          | rewrite heq ]
  end.


(** Preuve de complétude de la déduction naturelle. *)

Lemma completness : forall Γ A, Γ ⊧ A -> Γ ⊢ A.
Proof.
  intros Γ A H.
  remember (A :: Γ) as X.
  revert HeqX.
  revert Γ A H.
  pattern X.
  apply well_founded_induction with (R:=gammaLt).
  { exact gammaLt_wf. }
  intros x H Γ A H0 HeqX.
  pose (disj:= disjunction_gamma_formule Γ A).
  clearbody disj.
  decompose [ex or and] disj; clear disj;subst
  ;try (rename x0 into B; rename x1 into C)
  ; try infer_inv_remove.
  { (* Levy 3.3.1.1 *)
    generalize (conseqset_andl H0).
    generalize (conseqset_andr H0).
    intros H1 H2.
    apply andi.
    - apply H with (y:=(B :: Γ)); solve_gammalt.
    - apply H with (y:=(C :: Γ));solve_gammalt. }

  { (* Levy 3.3.1.2 *)
    generalize (conseqset_impe2 H0).
    intros H1.
    apply impi;subst.    
    apply H with (y:=C :: B :: Γ);solve_gammalt. } (* hackish *)

  { (* Levy 3.3.1.3 *)
    generalize (conseqset_or_notl H0).
    intros H1.
    assert (h:gammaLt (C :: (B ⇒ ⊥) :: Γ) ((B ∨ C) :: Γ)).
    { subst. solve_gammalt. } 
    generalize (H (C :: (B ⇒ ⊥) :: Γ) h ((B ⇒ ⊥) :: Γ) C).
    intros H2.
    apply impe with ((B⇒⊥)⇒C).
    - apply impi.
      apply or_imp.
    - apply impi.
      apply H2.
      + assumption.
      + reflexivity. }

  { assert (x0 :: Γ ⊢ ⊥).
    { apply H with (y := ⊥ :: x0 :: Γ);solve_gammalt.
      apply conseqset_neg.
      assumption. }
    apply noti.
    assumption. }


  red in H3.
  { rename x0 into ff.
    decompose [ex or and] H3; clear H3;subst ff;try (rename x into B; rename x0 into C).

  (* LEVY 3.3.1.4 *)
  { assert (B :: C :: Δ ⊧ A).
    { eapply conseqset_lande. instantiate (1:=Γ).
      - subst.
        rewrite ENV.remove_same_add_in;auto.
        reflexivity.
      - assumption. }
    assert (P:(B :: C :: Δ) ⊢ A).
    { apply H with (y:=A :: B :: C :: Δ);subst Δ;solve_gammalt.
        setoid_rewrite heq at 2.
        solve_gammalt. }
    apply impe_impi_add_double with B C;auto.
    + apply ande1 with C.
      tax.
    + apply ande2 with B.
      tax. }

  (* LEVY 3.3.1.5 *)
  { assert (B :: Δ ⊧ A).
    { eapply @conseqset_or_l with (C := C) (Γ' := Γ).
      - subst.
        rewrite ENV.remove_same_add_in;auto.
        reflexivity.
      - assumption. }
    assert (C :: Δ ⊧ A).
    { eapply @conseqset_or_r with (B := B) (Γ' := Γ).
      - subst.
        rewrite ENV.remove_same_add_in;auto.
        reflexivity.
      - assumption. }
    assert (B :: Δ ⊢ A).
    { apply H with (y:= A :: B :: Δ);subst;solve_gammalt.
      - rewrite heq at 2. (* why do we need to say at 2 here??? *)
        solve_gammalt. }
    assert (C :: Δ ⊢ A).
    { apply H with (y:= A :: C :: Δ);subst;solve_gammalt.
      rewrite heq at 2. (* why do we need to say at 2 here??? *)
      solve_gammalt. }
    apply ore with (φ₁:=B) (φ₂:=C).
    - tax.
    - rewrite ENV.add_comm.
      apply weakening.
      assumption.
    - rewrite ENV.add_comm.
      apply weakening.
      assumption. }

  (* LEVY 3.3.1.6 *)
  { assert ((¬B) :: Δ ⊧ A).
    { eapply @conseqset_imp_r with (C := C) (Γ' := Γ);subst;solve_gammalt. }
    assert (C :: Δ ⊧ A).
    { eapply @conseqset_imp_l with (B := B) (Γ' := Γ);subst;solve_gammalt. }
    assert ((¬B) :: Δ ⊢ A).
    { apply H with (y:=A :: (¬B) :: Δ);subst;solve_gammalt.
      rewrite heq at 2. (* why do we need to say at 2 here??? *)
      solve_gammalt.
      generalize (mesure_not_false _ H5).
      intros hh.
      lia. }
    assert (C :: Δ ⊢ A).
    { apply H with (y:= A :: C :: Δ);subst;solve_gammalt.
      rewrite heq at 2. (* why do we need to say at 2 here??? *)
      solve_gammalt. }
    apply ore with (φ₁:=¬B) (φ₂:=C).
    - apply ore with (φ₁:=B) (φ₂:=¬B).
      + apply (Exemple_DN.a_or_nota B).
      + apply ori2.
        apply impe with (φ₁:=B).
        * tax.
        * tax.
      + apply ori1.
        tax.
    - rewrite ENV.add_comm.
      apply weakening.
      assumption.
    - rewrite ENV.add_comm.
      apply weakening.
      assumption. }

  (* LEVY 3.3.1.7 *)
  { assert ((B ⇒ ⊥) :: Δ ⊧ A).
    { eapply @conseqset_notand_l with (C := C) (Γ' := Γ).
      - assumption.
      - assumption. }
    assert ((C ⇒ ⊥) :: Δ ⊧ A).
    { eapply @conseqset_notand_r with (B := B) (Γ' := Γ).
      - assumption.
      - assumption. }
    assert ((B⇒⊥) :: Δ ⊢ A).
    { apply H with (y:= A :: (B⇒⊥) :: Δ);subst;solve_gammalt.
      rewrite heq at 2. (* why do we need to say at 2 here??? *)
      solve_gammalt. }
    assert ((C⇒⊥) :: Δ ⊢ A).
    { apply H with (y:= A :: (C⇒⊥) :: Δ);subst;solve_gammalt.
      rewrite heq at 2. (* why do we need to say at 2 here??? *)
      solve_gammalt. }
    apply ore with (φ₁:=B⇒⊥) (φ₂:=C⇒⊥).
    - apply and_false_false_or.     (* LEVY exo 46 *)
    - setoid_rewrite ENV.add_comm at 1.
      apply weakening.
      assumption.
    - setoid_rewrite ENV.add_comm at 1.
      apply weakening.
      assumption. }

  (* LEVY 3.3.1.8 *)
  { assert ((B ⇒ ⊥) :: (C ⇒ ⊥) :: Δ ⊧ A).
    { eapply @conseqset_notor with (C := C) (Γ' := Γ).
      - assumption.
      - assumption. }
    assert ((B⇒⊥) :: (C⇒⊥) :: Δ ⊢ A).
    { apply H with (y:= A :: (B⇒⊥) :: (C⇒⊥) :: Δ);subst;solve_gammalt.
      rewrite heq at 2. (* why do we need to say at 2 here??? *)
      solve_gammalt. }
    apply impe with (φ₁:=(B ⇒ ⊥)).
    - apply impi.
      apply impe with (φ₁:=(C ⇒ ⊥)).
      + apply impi.
        setoid_rewrite ENV.add_comm at 2.
        setoid_rewrite ENV.add_comm at 1.
        apply weakening.
        setoid_rewrite ENV.add_comm at 1.
        assumption.
      + rewrite ENV.add_comm.
        apply not_or_and_not_2.
    - eapply not_or_and_not_1. }

  (* LEVY 3.3.1.9 *)
  { assert (B :: (C ⇒ ⊥) :: Δ ⊧ A).
    { eapply @conseqset_notimp.
      rewrite heq in H0.
      assumption. }
    assert (B :: (C⇒⊥) :: Δ ⊢ A).
    { apply H with (y:= A :: B :: (C⇒⊥) :: Δ);subst;solve_gammalt.
      rewrite heq at 2. (* why do we need to say at 2 here??? *)
      solve_gammalt. }

      apply impe with (φ₁:=B).
    - apply impi.
      apply impe with (φ₁:=(C ⇒ ⊥)).
      + apply impi.
        setoid_rewrite ENV.add_comm at 2.
        setoid_rewrite ENV.add_comm at 1.
        apply weakening.
        setoid_rewrite ENV.add_comm at 1.
        assumption.
      + rewrite ENV.add_comm.
        apply not_imp2. (* exo 48 Levy *)
    - apply not_imp. (* exo 48 Levy *) }

  (* Même cas en replaçant => false par not. *)
  { assert ((¬B) :: Δ ⊧ A).
    { eapply @conseqset_notand_l' with (C := C) (Γ' := Γ).
      - assumption.
      - assumption. }
    assert ((¬C) :: Δ ⊧ A).
    { eapply @conseqset_notand_r' with (B := B) (Γ' := Γ).
      - assumption.
      - assumption. }
    assert ((¬B) :: Δ ⊢ A).
    { apply H with (y:= A :: (¬B) :: Δ);subst;solve_gammalt.
      rewrite heq at 2. (* why do we need to say at 2 here??? *)
      solve_gammalt. }
    assert ((¬C) :: Δ ⊢ A).
    { apply H with (y:= A :: (¬C) :: Δ);subst;solve_gammalt.
      rewrite heq at 2. (* why do we need to say at 2 here??? *)
      solve_gammalt. }
    apply ore with (φ₁:=¬B) (φ₂:=¬C).
    - apply and_false_false_or'.     (* LEVY exo 46 *)
    - setoid_rewrite ENV.add_comm at 1.
      apply weakening.
      assumption.
    - setoid_rewrite ENV.add_comm at 1.
      apply weakening.
      assumption. }

  (* LEVY 3.3.1.8 *)
  { assert ((¬B) :: (¬C) :: Δ ⊧ A).
    { eapply @conseqset_notor' with (C := C) (Γ' := Γ).
      - assumption.
      - assumption. }
    assert ((¬B) :: (¬C) :: Δ ⊢ A).
    { apply H with (y:= A :: (¬B) :: (¬C) :: Δ);subst;solve_gammalt.
      rewrite heq at 2. (* why do we need to say at 2 here??? *)
      solve_gammalt. }
    apply impe with (φ₁:=(¬B)).
    - apply impi.
      apply impe with (φ₁:=(¬C)).
      + apply impi.
        setoid_rewrite ENV.add_comm at 2.
        setoid_rewrite ENV.add_comm at 1.
        apply weakening.
        setoid_rewrite ENV.add_comm at 1.
        assumption.
      + rewrite ENV.add_comm.
        apply not_or_and_not_2'.
    - eapply not_or_and_not_1'. }

  (* LEVY 3.3.1.9 *)
  { assert (B :: (¬C) :: Δ ⊧ A).
    { eapply @conseqset_notimp'.
      rewrite heq in H0.
      assumption. }
    assert (B :: (¬C) :: Δ ⊢ A).
    { apply H with (y:= A :: B :: (¬C) :: Δ);subst;solve_gammalt.
      rewrite heq at 2. (* why do we need to say at 2 here??? *)
      solve_gammalt. }

      apply impe with (φ₁:=B).
    - apply impi.
      apply impe with (φ₁:=(¬C)).
      + apply impi.
        setoid_rewrite ENV.add_comm at 2.
        setoid_rewrite ENV.add_comm at 1.
        apply weakening.
        setoid_rewrite ENV.add_comm at 1.
        assumption.
      + rewrite ENV.add_comm.
        apply not_imp2'. (* exo 48 Levy *)
    - apply not_imp'. (* exo 48 Levy *) }


  (* LEVY 3.3.1.9 modifiée pour (¬(¬φ)) *)
  { rename x into B.
    assert (B :: (¬⊥) :: Δ ⊧ A).
    { eapply @conseqset_notimp''.
      rewrite heq in H0.
      assumption. }
    assert (B :: (¬⊥) :: Δ ⊢ A).
    { apply H with (y:= A :: B :: (¬⊥) :: Δ);subst;solve_gammalt.
      rewrite heq at 2. (* why do we need to say at 2 here??? *)
      solve_gammalt. }

      apply impe with (φ₁:=B).
    - apply impi.
      apply impe with (φ₁:=(¬⊥)).
      + apply impi.
        setoid_rewrite ENV.add_comm at 2.
        setoid_rewrite ENV.add_comm at 1.
        apply weakening.
        setoid_rewrite ENV.add_comm at 1.
        assumption.
      + rewrite ENV.add_comm.
        apply noti.
        tax.
    - apply not_not_eq''. (* exo 48 Levy *) }

  (* LEVY 3.3.1.9 modifiée pour ((¬φ)⇒⊥) *)
  { rename x into B.
    assert (B :: (¬⊥) :: Δ ⊧ A).
    { eapply @conseqset_notimp'''.
      rewrite heq in H0.
      assumption. }
    assert (B :: (¬⊥) :: Δ ⊢ A).
    { apply H with (y:= A :: B :: (¬⊥) :: Δ);subst;solve_gammalt.
      rewrite heq at 2. (* why do we need to say at 2 here??? *)
      solve_gammalt. }

      apply impe with (φ₁:=B).
    - apply impi.
      apply impe with (φ₁:=(¬⊥)).
      + apply impi.
        setoid_rewrite ENV.add_comm at 2.
        setoid_rewrite ENV.add_comm at 1.
        apply weakening.
        setoid_rewrite ENV.add_comm at 1.
        assumption.
      + rewrite ENV.add_comm.
        apply noti.
        tax.
    - apply not_not_eq''''. (* exo 48 Levy *) }
  }

(* + les cas de bases 3.3.10 a)b)c) *)

  subst Δ.
  rewrite <- heq in *.
  destruct H3.

  { apply note with ⊤.
    - apply true_ax.
    - rewrite heq.
      tax. }
  { apply fale.
    apply weakening.
    rewrite heq.
    tax. }
  { apply note with ⊤.
    - apply true_ax.
    - apply noti.
      apply impe with ⊤.
      + apply weakening.
        rewrite heq.
        tax.
      + apply true_ax. }


(* + les cas de bases 3.3.10 a)b)c) *)
  destruct H3.
  { (* b- version ¬⊤  *)
    apply literaux_conseq_false_new in H0;auto.
    decompose [ex and or] H0;clear H0.
    - rename x into b.
      apply note with (Var b).
      + tax.
      + tax.
    - rename x into b.
      apply noti.
      apply impe with (Var b).
      + tax.
      + tax. }
  { (* a) *)    
    apply literaux_conseq_false_new in H0;auto.
    decompose [ex and or] H0;clear H0.
    - rename x into b.
      apply note with (Var b).
      + tax.
      + tax.
    - rename x into b.
      apply impe with (Var b).
      + tax.
      + tax. }

  { (* b- version ⊤ ⇒ ⊥  *)
    apply literaux_conseq_false_new in H0;auto.
    decompose [ex and or] H0.
    - rename x into b.
      apply impi.
      apply note with (Var b).
      + tax.
      + tax.
    - rename x into b.
      apply impi.
      apply impe with (Var b).
      + tax.
      + tax. }

  destruct H3.
  { (* 10.c *)
    apply literaux_conseq in H0;auto.
    decompose [ex and or] H0.
    - rename x into b.
      apply note with (Var b).
      + tax.
      + tax.
    - rename x into b.
      apply note with (Var b).
      + tax.
      + apply noti.
        apply impe with (Var b).
        * tax.
        * tax.
    - tax. }

  { (* Pas vu où ce cas est traitée dans la preuve de M. Levy/ φ = x ⇒ ⊥? *)
    apply literaux_conseq_neg in H0;auto.
    decompose [ex and or] H0; clear H0.
    - rename x into b.
      apply note with (Var b).
      + tax.
      + tax.
    - rename x into b.
      apply note with (Var b).
      + tax.
      + apply noti.
        apply impe with (Var b).
        * tax.
        * tax.
    - tax.
    - apply noti.
      apply impe with (Var n).
      * tax.
      * tax. }

  { (* Pas vu où ce cas est traitée dans la preuve de M. Levy/ φ = x ⇒ ⊥? *)
    apply literaux_conseq_neg in H0;auto.
    decompose [ex and or] H0; clear H0.
    - rename x into b.
      apply note with (Var b).
      + tax.
      + tax.
    - rename x into b.
      apply note with (Var b).
      + tax.
      + apply noti.
        apply impe with (Var b).
        * tax.
        * tax.
    - apply impi.
      apply note with (Var n).
      * tax.
      * tax.
    - tax. }

  { apply true_ax. }

  { apply noti.
    tax. }

  { apply impi.
    tax. }
Qed.

Print Assumptions completness.


Lemma dn_equiv_compat: forall φ φ' Γ, (φ ≡ φ') -> Γ ⊢ φ -> Γ ⊢ φ'.
Proof.
  intros φ φ' Γ H H0. 
  apply soundness in H0.
  apply completness.
  intro v.
  intro hΓ.
  rewrite <- H.
  now apply H0.
Qed.

Global Instance dn_compat: Proper (ENV.eq ==> equiv ==> iff) pf.
Proof.
  repeat intro.
  transitivity (y ⊢ x0).
  { split;intro; eapply  equiv_gamma;eauto.
    now symmetry. }
  split;intro; eapply dn_equiv_compat;eauto.
  now symmetry.
Qed.


