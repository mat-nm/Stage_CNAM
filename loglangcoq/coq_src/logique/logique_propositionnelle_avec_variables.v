(** remove printing -> *)
(** remove printing forall *)
(** remove printing exists *)
(** remove printing ~ *)
(** remove printing => *)
(** printing -> $\longrightarrow$ #&#10230;# *)
(*moche printing => $\longrightarrow$ #&#10233;# *)

(** %\chapter{Logique propositionnelle}%#<h1 class="libtitle">Logique propositionnelle</h1># *)

(** Ce module formalise la logique propositionnelle (calcul
    propositionnel avec variables propositionnelles). *)

(* begin hide *)
From Stdlib Require Import Morphisms FunInd  OrderedType Setoid EqNat.
Require Import tables_de_verite logique_generique.
Local Notation ℕ := nat.
(* end hide *)

(** * Le formules propositionnelle avec variables propositionnelles *)

(** ** Définition des formules *)

(** Les formules sont définies (par induction) par la grammaire suivante. *)

Inductive formule : Type :=
| Vrai: formule
| Faux: formule
| Var: ℕ -> formule (** On désigne les variables par des entiers. *)
| Non: formule -> formule
| Ou: formule -> formule -> formule
| Et: formule -> formule -> formule
| Implique: formule -> formule -> formule.

(** ** Exemples de formules sans notation *)

(**
[
Check Vrai.
Check Faux.
Check (Var 23).
Check (Ou Vrai Vrai).
Check (Ou Faux Vrai).
Check (Ou (Ou Vrai Faux) Vrai).
] *)

(** ** Notations usuelles *)

(* begin hide *)
Module Notations.
Reserved Notation  "X ∨ Y" (at level 85,right associativity).
Reserved Notation "X ∧ Y" (at level 82,right associativity).
Reserved Notation "¬ X" (at level 80).
Reserved Notation "X ⇒ Y" (at level 86,right associativity).
(* end hide *)

Notation "⊤":= Vrai: formule_scope .
Notation "⊥":= Faux: formule_scope .
Notation "¬ X":= (Non X): formule_scope .
Notation "X ∨ Y":= (Ou X Y): formule_scope .
Notation "X ∧ Y":= (Et X Y): formule_scope .
Notation "X ⇒ Y":= (Implique X Y): formule_scope .

(** Les variables seront également plus lisibles en notant le numéro de
    la variable en indice de la lettre [X] ('x' majuscule). *)

Notation "'X₁'":= (Var 1): formule_scope.
Notation "'X₂'":= (Var 2): formule_scope.
(* begin hide *)
Notation "'X₃'":= (Var 3): formule_scope.
Notation "'X₄'":= (Var 4): formule_scope.
Notation "'X₅'":= (Var 5): formule_scope.
Notation "'X₆'":= (Var 6): formule_scope.
Notation "'X₇'":= (Var 7): formule_scope.
Notation "'X₈'":= (Var 8): formule_scope.
Notation "'X₉'":= (Var 9): formule_scope.
Notation "'X₁₀'":= (Var 10): formule_scope.
End Notations.
(* end hide *)

(** ** Exemples avec les notations usuelles *)

(**
[
Check ⊤.
Check ⊥.
Check X₇.
Check (⊤ ∨ ⊤).
Check (⊤ ∨ X₃).
Check (X₉ ∨ X₂).
Check ((⊤ ∨ X₄) ∨ ⊤).
]
*)

(** * Interprétation d'une formule (Sémantique) *)

(** ** Définition de l'interprétation d'une formule *)

(** Définition de l'interprétation d'une formule. Pour interpréter
    les variables propositionnelles on a besoin d'une valuation
    [v] des variables vers les valeurs de vérité ([bool]), ensuite on
    applique les tables de vérité des feuilles jusqu'à la racine comme
    le calcul propositionnel. *)

Import Notations.

Function interp_def (v:nat -> bool)  (f:formule) : bool :=
  match f with
    | ⊤ => table_Vrai
    | ⊥ => table_Faux
    | Var i => v i
    | ¬ f => table_Non (interp_def v f)
    | f₁ ∨ f₂ => table_Ou (interp_def v f₁) (interp_def v f₂)
    | f₁ ∧ f₂ => table_Et (interp_def v f₁) (interp_def v f₂)
    | f₁ ⇒ f₂ => table_Implique (interp_def v f₁) (interp_def v f₂)
  end.

(** ** quelques exemples

Voir plus bas pour plus d'exemples. *)

(* begin hide *)
(**
[
Module Exemples_interp_def.
  (* end hide *)
  Eval compute in interp_def (fun x => true) (Implique ⊤ (Ou ⊤ ⊥)). (** → true *)

  Eval compute in interp_def (fun x => false) (Implique ⊤ (Ou ⊤ ⊥)). (** → true *)

  Eval compute in interp_def (fun x => false) (Implique ⊤ (Ou ⊥ ⊥)). (** → false *)

  Definition val_X₁_true := (fun x => match x with 1 => true | _ => false end).

  Definition val_X₁_false := (fun x => match x with 1 => false | _ => false end).

  Eval compute in interp_def val_X₁_true (Implique ⊤ (Ou ⊥ X₁)). (** → true *)

  Eval compute in interp_def val_X₁_false (Implique ⊤ (Ou ⊥ X₁)). (** → false *)
  (* begin hide *)
End Exemples_interp_def.
]*)
(* end hide *)

(* ** Version "optimisée" de l'interprétation *)

(** Version optimisée qui n'évalue la sous-formule de droite que si
    nécessaire. *)

Function interp (v:nat -> bool) (f:formule) : bool :=
  match f with
    | ⊤ => true
    | ⊥ => false
    | Var i => v i
    | ¬f => if interp v f then false else true
    | f₁ ∨ f₂ => if interp v f₁ then true else interp v f₂
    | f₁ ∧ f₂ => if interp v f₁ then interp v f₂ else false
    | f₁ ⇒ f₂ => if interp v f₁ then interp v f₂ else true
  end.

(** ** Preuve de correction de la version optimisée. *)

Lemma interp_correct: forall I:ℕ -> bool,forall f:formule, interp_def I f = interp I f.
Proof.
  induction f.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. repeat rewrite IHf.
    simpl. destruct (interp I f);simpl;reflexivity.
  - simpl. repeat rewrite IHf1, IHf2.
    simpl. destruct (interp I f2); destruct (interp I f1);simpl;reflexivity.
  - simpl. repeat rewrite <- IHf1, <- IHf2.
    destruct (interp I f2); destruct (interp I f1);simpl;
    repeat rewrite IHf1, IHf2;simpl; reflexivity.
  - simpl. repeat rewrite IHf1, IHf2.
    simpl. destruct (interp I f2); destruct (interp I f1);simpl;reflexivity.
Qed.


(** ** Exemples d'interprétations *)
(* begin hide *)
Module Exemples_interp.
  (* end hide *)
  Definition v₁ (n:nat): bool :=
    match n with
      | 1 => true
      | 2 => false
      | 3 => true
      | _ => false
    end.

  Definition v₂ (n:nat): bool :=
    match n with
      | 1 => false
      | 2 => true
      | 3 => true
      | _ => false
    end.

(**
[
  Eval compute in interp_def v₁ (Implique Vrai (Ou Vrai Faux)). (** → true *)

  Eval compute in interp_def v₂ (Implique Vrai (Ou Vrai Faux)). (** → true *)

  Eval compute in interp_def v₁ (Implique Vrai (Ou Faux Faux)). (** → false *)

  Eval compute in interp_def v₂ (Implique Vrai (Ou Faux Faux)). (** → false *)

  Eval compute in interp_def v₁ X₂. (** → false *)

  Eval compute in interp_def v₁ X₂. (** → false *)

  Eval compute in interp_def v₂ X₂.  (** → true *)

  Eval compute in interp_def v₁ (Implique X₁ (Ou Faux Faux)). (** → false *)

  Eval compute in interp_def v₂ (Implique X₁ (Ou Faux Faux)). (** → true *)

  Eval compute in interp v₁ (Implique Vrai (Ou Vrai Faux)). (** → true *)

  Eval compute in interp v₂ (Implique Vrai (Ou Vrai Faux)). (** → true *)

  Eval compute in interp v₁ (Implique Vrai (Ou Faux Faux)). (** → false *)

  Eval compute in interp v₂ (Implique Vrai (Ou Faux Faux)). (** → false *)

  Eval compute in interp v₁ X₂. (** → false *)

  Eval compute in interp v₁ X₂. (** → false *)

  Eval compute in interp v₂ X₂. (** → true *)

  Eval compute in interp v₁ (Implique X₁ (Ou Faux Faux)). (** → false *)

  Eval compute in interp v₂ (Implique X₁ (Ou Faux Faux)). (** → true *)
] *)

  (* begin hide *)
End Exemples_interp.
(* end hide *)

(** * Conséquence, modèle etc *)

(** On applique les définitions de conséquence, modèle etc du
    chapitre %\og\coqref{logique generique}{logique generique}\fg{}%#<a href="logique_generique.html">logique_generique</a>#
    avec les notions de valuation et d'interprétation ci-dessous. *)

(* begin hide *)
Scheme Equality for formule.

Function formule_eq (φ ψ:formule)  {struct φ}: Prop := 
  match φ,ψ with 
    | ⊤,⊤ => True
    | ⊥,⊥ => True
    | Var p,Var q => EqNat.eq_nat p q
    |  φ₁ ⇒ φ₂, ψ₁ ⇒ ψ₂ => formule_eq φ₁ ψ₁ /\ formule_eq φ₂ ψ₂
    | φ₁ ∧ φ₂,ψ₁ ∧ ψ₂ => formule_eq φ₁ ψ₁ /\ formule_eq φ₂ ψ₂
    | φ₁ ∨ φ₂,ψ₁ ∨ ψ₂ => formule_eq φ₁ ψ₁ /\ formule_eq φ₂ ψ₂
    | ¬φ,¬ψ => formule_eq φ ψ
    | _,_ => False
  end.
(* end hide *)
(* begin hide *)
Module LogPropVar<: Logique.
  
  Definition formule := formule.
  Definition t := formule.
  Definition eq := @Logic.eq formule.
  Lemma eq_refl : forall x : formule, eq x x.
  Proof.
    intros x.
    apply @eq_refl.
  Qed.
  Lemma eq_sym : forall x y : formule, eq x y -> eq y x.
  Proof.
    intros x y.
    apply @eq_sym.
  Qed.
  Lemma eq_trans : forall x y z : formule, eq x y -> eq y z -> eq x z.
  Proof.
    intros x y z.
    apply @eq_trans.
  Qed.

  Lemma eq_dec : forall x y : formule, {eq x y} + {~ eq x y}.
  Proof.
    exact formule_eq_dec.
  Defined.
  (* end hide *)

  Definition valuation: Type:= ℕ -> bool.

  (** Dans la suite on écrira [interpretation v φ b] plutôt que
      [interp_def v φ = b]. *)

  Definition interpretation := fun v φ b => interp_def v φ = b.
  
  (* begin hide *)
  Lemma interpretation_unique:
    forall v f b1 b2, interpretation v f b1 -> interpretation v f b2 -> b1= b2.
  Proof.
    intros v f b1 b2 H H0.
    unfold interpretation in *.
    subst;reflexivity.
  Qed.
  (* end hide *)

  (** Résultat supplémentaire: l'interprétation est décidable. Ce ne
      sera pas le cas pour la logique des prédicats avec
      quantificateurs *)

  Lemma interpretation_dec:
    forall v φ, interpretation v φ true \/ interpretation v φ false.
  Proof.
    intros v f.
    unfold interpretation.
    destruct (interp_def v f);simpl;auto.
  Qed.
  (* begin hide *)
End LogPropVar.
(* end hide *)

(* begin hide *)

Import LogPropVar.

Module Import LogPropVarEnv:=Environnement(LogPropVar). 
Import LogPropVarEnv.DEFS.
(* Open Scope logique_scope. *)

Ltac smpl := unfold interpretation, equiv, consequence, est_modele,
             consequence, est_modele_set in *;simpl in *.
Tactic Notation "smpl*" := repeat progress smpl.
(* end hide *)

(** Une autre définition pour l'équivalence: l'interprétation des deux
    formules est toujours identique.  *)
(* QUESTION: est-ce toujours vrai, en particulier lorsque
   l'interprétation n'est plus décidable. *)

Definition equivalent φ₁ φ₂ :=
  forall I b, (interpretation I φ₁ b)<->(interpretation I φ₂ b).

(** Preuve d'equivalence entre les deux notions d'équivalence. *)

Lemma equivEquivalence :forall φ₁ φ₂,(DEFS.equiv φ₁ φ₂) <-> (equivalent φ₁ φ₂).
  intros φ₁ φ₂.
  unfold equivalent.
  smpl*.
  split.
  - intros [h1 h2] I.
    specialize (h1 I).
    specialize (h2 I).
    destruct (interp_def I φ₂);destruct (interp_def I φ₁);simpl;intros;auto;try reflexivity;try now discriminate.
    + discriminate h2;reflexivity.
    + discriminate h1;reflexivity.
  - intros h.
    split; intros I h'.
    + apply h;assumption.
    + apply h;assumption.
Qed.


(** ** Exemple de modèles et de conséquences *)
(* begin hide *)
Module Exemples_modeles.
  (* end hide *)

  Lemma modele1 : forall v, ⊧[v] X₁ ∨ ¬ X₁.
  Proof.
    intros v.
    red.
    simpl.
    destruct (v 1).
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma modele2 : forall v, ⊧[v] (X₁ ∨ ¬ X₂) ∨ X₂.
  Proof.
    intros v.
    red.
    simpl.
    destruct (v 1).
    - destruct (v 2);simpl.
      + reflexivity.
      + reflexivity.
    - destruct (v 2).
      + reflexivity.
      + reflexivity.
  Qed.
  (* begin hide *)
End Exemples_modeles.
(* end hide *)


(* begin hide *)
Module Exemples_conseq.
  (* end hide *)
  Lemma conseq1: (X₁∨¬X₂) ∧ X₂ ⊧ X₁.
  Proof.
    repeat red.
    simpl.
    intros I H.
    red in H.
    simpl in *.
    destruct (I 1).
    - reflexivity.
    - destruct (I 2).
      + discriminate H.
      + discriminate H.
  Qed.

  (* begin hide *)
End Exemples_conseq.
(* end hide *)

(** * Preuves d'équivalences entre formules *)

Lemma eq_implique : forall φ ψ : formule, φ ⇒ ψ ≡ ¬φ ∨ ψ.
Proof.
  intros φ ψ.
  simpl.
  unfold equiv,consequence,est_modele. simpl.
  split;intros v h.
  - functional inversion h;subst;clear h.
    + reflexivity.
    + simpl.
      destruct (interp_def v ψ);simpl;auto.
  - destruct (interp_def v φ).
    + assumption.
    + reflexivity.
Qed.

Lemma eq_et : forall φ ψ: formule, (φ ∧ ψ) ≡ ¬ (¬φ ∨ ¬ψ).
Proof.
  intros φ ψ.
  unfold equiv,consequence,est_modele. simpl.
  split;intros v h.
  - functional inversion h;subst;clear h.
    reflexivity.
  - destruct (interp_def v φ).
    + destruct (interp_def v ψ).
      * reflexivity.
      * discriminate.
    + destruct (interp_def v ψ).
      * discriminate.
      * discriminate.
Qed.

Lemma eq_not_true : ⊥ ≡ ¬ ⊤.
Proof.
  simpl.
  unfold equiv,consequence,est_modele. simpl.
  split;intros.
  - discriminate.
  - discriminate.
Qed.

Lemma eq_not_false : ⊤ ≡ ¬ ⊥.
Proof.
  simpl.
  unfold equiv,consequence,est_modele. simpl.
  split;intros.
  - reflexivity.
  - reflexivity.
Qed.

(* begin hide *)

Lemma equiv_refl: forall φ, φ ≡ φ.
Proof.
  split;red;auto.
Qed.

Lemma equiv_sym: forall φ₁ φ₂, (φ₁ ≡ φ₂) -> (φ₂ ≡ φ₁).
Proof.
  split;red;intros;red in H;destruct H;auto.
Qed.

Lemma equiv_trans: forall φ₁ φ₂ φ₃, (φ₁ ≡ φ₂) -> (φ₂ ≡ φ₃) -> (φ₁ ≡ φ₃).
Proof.
  unfold equiv, consequence, est_modele in *.
  intros φ₁ φ₂ φ₃ H H0.
  destruct H. destruct H0.
  split;auto.
Qed.

Add Parametric Relation : formule equiv
    reflexivity proved by equiv_refl
    symmetry proved by equiv_sym
    transitivity proved by equiv_trans
      as equiv_rel.

Add Parametric Morphism: interp_def
    with signature Logic.eq ==> equiv ==> Logic.eq as interp_morphism.
Proof.
  intros v x y0.
  unfold equiv, consequence, est_modele.
  destruct 1.
  specialize (H v).
  specialize (H0 v).
  destruct (interp_def v x);destruct (interp_def v y0);try reflexivity;auto.
  symmetry;auto.
Qed.


Add Parametric Morphism: Et
    with signature equiv ==> equiv ==> equiv as and_morphism.
Proof.
  intros x y [h1 h2] x0 y0 [h3 h4].
  unfold equiv, consequence, est_modele in *.
  simpl;split;intros v h.
  - simpl in h.
    functional inversion h;subst;clear h.
    rewrite h1;auto.
    rewrite h3;auto.
  - functional inversion h;subst;clear h.
    rewrite h2;auto.
    rewrite h4;auto.
Qed.

Add Parametric Morphism: Ou
    with signature equiv ==> equiv ==> equiv as Ou_morphism.
Proof.
  intros x y [h1 h2] x0 y0 [h3 h4].
  unfold equiv, consequence, est_modele in *.
  simpl;split;intros v h.
  - functional inversion h;subst;clear h.
    + rewrite h1;auto.
      destruct (interp_def v y0);auto.
    + rewrite h1;auto.
      destruct (interp_def v y0);auto.
    + rewrite h3;auto.
      destruct (interp_def v y);auto.      
  - functional inversion h;subst;clear h.
    + rewrite h2;auto.
      destruct (interp_def v x0);auto.
    + rewrite h2;auto.
      destruct (interp_def v x0);auto.
    + rewrite h4;auto.
      destruct (interp_def v x);auto.      
Qed.

Add Parametric Morphism: Non
    with signature equiv ==> equiv as Non_morphism.
Proof.
  intros x y [h1 h2].
  smpl*.
  split;intros v h.
  - functional inversion h;subst;clear h.    
    specialize (h2 v).
    destruct (interp_def v y);auto.
    rewrite h2 in H.
    + discriminate.
    + reflexivity.
  - functional inversion h;subst;clear h.
    specialize (h1 v).
    destruct (interp_def v x);auto.
    rewrite h1 in H.
    + discriminate.
    + reflexivity.
Qed.

Add Parametric Morphism: Implique
    with signature equiv ==> equiv ==> equiv as Implique_morphism.
Proof.
  intros x y [h1 h2] x0 y0 [h3 h4].
  smpl*.
  split;intros v h.
  - functional inversion h;subst;clear h.
    + rewrite h1;auto.
      rewrite h3;auto.
    + specialize (h2 v).
      setoid_rewrite <- H in h2.
      destruct (interp_def v y);auto.
      specialize (h2 Logic.eq_refl).
      discriminate.
  - functional inversion h;subst;clear h.
    + rewrite h4;auto.
      destruct (interp_def v x);auto.
    + specialize (h1 v).
      setoid_rewrite <- H in h1.
      destruct (interp_def v x);auto.
      specialize (h1 Logic.eq_refl).
      discriminate.
Qed.


Add Parametric Morphism: est_modele
    with signature Logic.eq ==> equiv ==> iff as estmodele_morphism.
Proof.
  intros v x y [h1 h2].
  unfold equiv, consequence, est_modele in *.
  simpl;split;intro h;auto.
Qed.

Add Parametric Morphism: consequence
    with signature equiv ==> equiv ==> iff as conseq_morphism.
Proof.
  intros x y [h1 h2] x0 y0 [h3 h4].
  unfold equiv, consequence, est_modele in *.
  simpl;split;intros h v h';auto.
Qed.

(* end hide *)

(** * Réduction des connecteurs au sous-ensemble {⊤,¬,∨} *)

(** Fonction qui remplace les formules contenant les autres
      connecteurs par des formule équivalentes. *)

Function reduce (f:formule) : formule :=
  match f with
    | ⊤ => ⊤
    | ⊥ => ¬ ⊤
    | Var i => Var i
    | ¬ f => ¬ (reduce f)
    | f₁ ∨ f₂ => (reduce f₁) ∨ (reduce f₂)
    | f₁ ∧ f₂ => ¬ (¬ (reduce f₁) ∨ ¬ (reduce f₂))
    | f₁ ⇒ f₂ => ¬ (reduce f₁) ∨ (reduce f₂)
  end.


Lemma reduce_correct:
  forall v, forall f:formule, interp_def v f = interp_def v (reduce f).
Proof.
  intros v f.
  induction f.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite IHf. reflexivity.
  - simpl. rewrite IHf1, IHf2. reflexivity.
  - simpl. repeat rewrite <- IHf1, <- IHf2.
    destruct (interp_def v f1).
    + destruct (interp_def v f2).
      * reflexivity.
      * reflexivity.
    + destruct (interp_def v f2).
      * reflexivity.
      * reflexivity.
  - simpl. rewrite <- IHf1, <- IHf2.
    destruct (interp_def v f1).
    + reflexivity.
    + destruct (interp_def v f2).
      * reflexivity.
      * reflexivity.
Qed.


Lemma reduce_equiv : forall f:formule, f ≡ (reduce f).
Proof.
  intros f.
  unfold equiv , consequence, est_modele.
  split;intros.
  - rewrite <- reduce_correct.
    assumption.
  - rewrite reduce_correct.
    assumption.
Qed.

(** Propriété d'être formé uniquement avec des ¬, ∨ et ⊤ ou Var. *)

Inductive is_reduced : formule -> Prop :=
  Vrai_is_red: is_reduced ⊤
| Var_is_red: forall i, is_reduced (Var i)
| Non_is_red: forall f,is_reduced f -> is_reduced (¬ f)
| Or_is_red: forall f g,is_reduced f -> is_reduced g -> is_reduced (f ∨ g).

(** la fonction [reduce] retourne bien une formule de cette forme. *)

Lemma reduce_complete : forall f, is_reduced (reduce f).
Proof.
  induction f.
  - simpl. apply Vrai_is_red.
  - simpl. apply Non_is_red. apply Vrai_is_red.
  - apply Var_is_red.
  - simpl. apply Non_is_red. assumption.
  - simpl. apply Or_is_red.
    + assumption.
    + assumption.
  - simpl. apply Non_is_red. apply Or_is_red.
    + apply Non_is_red. assumption.
    + apply Non_is_red. assumption.
  - simpl. apply Or_is_red.
    + apply Non_is_red. assumption.
    + assumption.
Qed.


(** * Preuve par réfutation (Utile pour la preuve par tableau plus loin).  *)

Lemma conseq_by_contradiction': forall f₁ f₂: formule, f₁ ⊧ f₂ -> f₁ ∧ ¬f₂ ⊧ ⊥.
Proof.
  intros f₁ f₂.
  unfold consequence, est_modele.
  intros H v H0.
  simpl in H0.
  destruct (interp_def v f₁) eqn:heq.
  - assert (heq':interp_def v f₂ = true).
    { apply H. apply heq. }
    rewrite heq' in H0.
    discriminate H0.
  - simpl in H0.
    destruct (interp_def v f₂);auto.
Qed.

(** Pour prouver f ⊧ g on peut prouver f ∧ ¬g ⊧ ⊥.  *)

Lemma conseq_by_contradiction: forall f₁ f₂: formule, f₁ ∧ ¬f₂ ⊧ ⊥ -> f₁ ⊧ f₂.
Proof.
  intros f₁ f₂.
  unfold consequence, est_modele.
  simpl.
  intros H v heq.
  specialize (H v).
  rewrite heq in H.
  destruct (interp_def v f₂) eqn:heq'.
  - reflexivity.
  - discriminate H. reflexivity.
Qed.

(** * Preuve par la méthode des tableaux  *)
(** 
   ------------------------------------------------------------
   ------------------------------------------------------------

*)


(** ** Lemmes auxilaires  *)

Lemma and_affaiblissement_conseq : forall v f₁ f₂, ⊧[v] f₁∧f₂ -> ⊧[v]f₁.
Proof.
  intros v f₁ f₂ H.
  red in H. red. simpl in *.
  destruct (interp_def v f₁).
  - reflexivity.
  - destruct (interp_def v f₂);auto; try discriminate .
Qed.

Lemma and_affaiblissement_contr : forall f₁ f₂, f₁ ⊧ ⊥ -> f₁∧f₂ ⊧ ⊥.
Proof.
  intros f₁ f₂ H.
  red in H. red.
  intros v H0.
  apply H.
  apply and_affaiblissement_conseq with (f₂ := f₂).
  assumption.
Qed.

Lemma Et_sym : forall f₁ f₂, f₁ ∧ f₂ ≡ f₂ ∧ f₁.
Proof.
  intros f₁ f₂.
  split.
  - red;red;simpl.
    intros v H.
    red in H.
    simpl in H.
    destruct (interp_def v f₁).
    + destruct (interp_def v f₂).
      * assumption.
      * discriminate H.
    + destruct (interp_def v f₂).
      * assumption.
      * discriminate H.
  - red;red;simpl.
    intros v H.
    red in H.
    simpl in H.
    destruct (interp_def v f₁).
    + destruct (interp_def v f₂).
      * assumption.
      * discriminate H.
    + destruct (interp_def v f₂).
      * discriminate H.
      * discriminate H.
Qed.


Lemma Et_assoc : forall f₁ f₂ f₃, f₁ ∧ (f₂ ∧ f₃) ≡ (f₁ ∧ f₂) ∧ f₃.
Proof.
  intros f₁ f₂ f₃.
  split.
  - repeat red; simpl.
    intros v H.
    red in H.
    simpl in H.
    destruct (interp_def v f₁); destruct (interp_def v f₂); destruct (interp_def v f₃); try assumption; try discriminate.
  - repeat red; simpl.
    intros v H.
    red in H.
    simpl in H.
    destruct (interp_def v f₁); destruct (interp_def v f₂); destruct (interp_def v f₃); try assumption; try discriminate.
Qed.


Function extraction_disjuntion (f F: formule): option formule :=
  match F with
    | g ∧ F' =>
      if formule_eq_dec f g then Some F'
      else
        if formule_eq_dec f F' then Some g (* comme ça pas de true à mettre à la fin *)
        else 
          match extraction_disjuntion f F' with
              None => None
            | Some F'' => Some (g ∧ F'')
          end
    | g => if formule_eq_dec f g then Some ⊤ else None (* à éviter car un true apparaît en plus *)
  end.


(** [
Eval compute in (extraction_disjuntion  (¬X₁) (((X₁ ∨ ¬X₂) ∧ X₂) ∧ ¬X₁ ∧ X₂)).
Eval compute in (extraction_disjuntion  (¬X₁) (((X₁ ∨ ¬X₂) ∧ X₂) ∧ ¬X₁)).
Eval compute in (extraction_disjuntion  ((X₁ ∨ ¬X₂) ∧ X₂) (((X₁ ∨ ¬X₂) ∧ X₂) ∧ ¬X₁)). ] *)


Lemma Et_et_true : forall f, f ≡ f ∧ ⊤.
Proof.
  intros f.
  rewrite Et_sym.
  unfold equiv,consequence,est_modele.
  split;intros;simpl.
  - rewrite H.
    reflexivity.
  - functional inversion H.
    functional inversion H2.
    subst;simpl in *.
    symmetry.
    assumption.
Qed.    

Lemma extraction_disjuntion_ok :
  forall f F F', extraction_disjuntion f F = Some F' -> (F ≡ f ∧ F').
Proof.
  intros f F.
  functional induction (extraction_disjuntion f F);simpl;intros; try discriminate.
  - inversion H;subst;reflexivity.
  - inversion H;clear H.
    subst.
    setoid_rewrite Et_sym at 1.
    reflexivity.
  - inversion H;clear H.
    subst.
    rewrite (IHo _ e2).
    rewrite Et_assoc at 1.
    setoid_rewrite Et_sym at 2.
    rewrite <- Et_assoc at 1.
    reflexivity.
  - inversion H. clear H.
    subst.
    apply Et_et_true.
Qed.


(** ** Les règles des tableaux *)

Lemma tableau_Ou :
  forall F f₁ f₂, ((f₁ ∧ F ⊧ ⊥) /\ (f₂ ∧ F ⊧ ⊥)) -> (f₁ ∨ f₂) ∧ F ⊧ ⊥.
Proof.
  intros F f₁ f₂ [h h'].
  unfold consequence,est_modele,equiv in *.
  intros v H0.
  simpl in *.
  specialize (h v).
  specialize (h' v).
  apply h.
  destruct (interp_def v f₁);destruct (interp_def v f₂);destruct (interp_def v F);auto.
Qed.

Lemma tableau_Ou' : forall f₁ f₂, (f₁ ⊧ ⊥) /\ (f₂ ⊧ ⊥) -> (f₁ ∨ f₂) ⊧ ⊥.
Proof.
  intros f₁ f₂ [h h'].
  unfold consequence,est_modele,equiv in *.
  intros v H0.
  simpl in *.
  specialize (h v).
  specialize (h' v).
  apply h.
  destruct (interp_def v f₁);destruct (interp_def v f₂);auto.
Qed.


Lemma tableau_nonEt:
  forall F f₁ f₂, (¬f₁ ∧ F ⊧ ⊥) /\ (¬f₂ ∧ F ⊧ ⊥) -> ¬(f₁ ∧ f₂) ∧ F ⊧ ⊥.
Proof.
  intros F f₁ f₂ H.
  destruct H as [h h'].
  unfold consequence,est_modele,equiv in *.
  intros v H0.
  specialize (h v).
  specialize (h' v).
  apply h.
  simpl in *.
  destruct (interp_def v f₁);destruct (interp_def v f₂);destruct (interp_def v F);auto.
Qed.

Lemma tableau_nonEt' : forall f₁ f₂, (¬f₁ ⊧ ⊥) /\ (¬f₂ ⊧ ⊥) -> ¬(f₁ ∧ f₂) ⊧ ⊥.
Proof.
  intros f₁ f₂ H.
  destruct H as [h h'].
  unfold consequence,est_modele,equiv in *.
  intros v H0.
  specialize (h v).
  specialize (h' v).
  apply h.
  simpl in *.
  destruct (interp_def v f₁);destruct (interp_def v f₂);auto.
Qed.

Lemma tableau_implique : 
  forall F f₁ f₂, (¬f₁ ∧ F ⊧ ⊥) /\ (f₂ ∧ F ⊧ ⊥) -> (f₁ ⇒ f₂) ∧ F ⊧ ⊥.
Proof.
  intros F f₁ f₂ H.
  destruct H as [h h'].
  unfold consequence,est_modele,equiv in *.
  intros v H0.
  specialize (h v).
  specialize (h' v).
  apply h.
  simpl in *.
  destruct (interp_def v f₁);destruct (interp_def v f₂)
  ;destruct (interp_def v F);auto.
Qed.

Lemma tableau_implique' : forall f₁ f₂, (¬f₁ ⊧ ⊥) /\ (f₂ ⊧ ⊥) -> (f₁ ⇒ f₂) ⊧ ⊥.
Proof.
  intros f₁ f₂ H.
  destruct H as [h h'].
  unfold consequence,est_modele,equiv in *.
  intros v H0.
  specialize (h v).
  specialize (h' v).
  apply h.
  simpl in *.
  destruct (interp_def v f₁);destruct (interp_def v f₂);auto.
Qed.

Lemma tableau_Et: forall F f₁ f₂, f₁ ∧ f₂ ∧ F ⊧ ⊥ -> (f₁ ∧ f₂) ∧ F ⊧ ⊥.
Proof.
  intros F f₁ f₂ h.
  unfold consequence,est_modele,equiv in *.
  simpl in *.
  intros v H0.
  specialize (h v).
  destruct (interp_def v f₁);destruct (interp_def v f₂);destruct (interp_def v F);auto.
Qed.

(*Lemma tableau_Et': forall f₁ f₂, f₁ ∧ f₂ ⊧ ⊥ -> (f₁ ∧ f₂) ⊧ ⊥.
Proof.
  intros F f₁ f₂ h.
  unfold consequence,est_modele,equiv in *.
  simpl in *.
  intros v H0.
  specialize (h v).
  destruct (interp_def v f₁);destruct (interp_def v f₂);destruct (interp_def v F);auto.
Qed.
 *)

Lemma tableau_nonimplique : forall F f₁ f₂, f₁ ∧ ¬f₂ ∧ F ⊧ ⊥ -> ¬(f₁ ⇒ f₂) ∧ F ⊧ ⊥.
Proof.
  intros F f₁ f₂ h.
  unfold consequence,est_modele,equiv in *.
  simpl in *.
  intros v H0.
  specialize (h v).
  destruct (interp_def v f₁);destruct (interp_def v f₂);destruct (interp_def v F);auto.
Qed.

Lemma tableau_nonimplique' : forall f₁ f₂, f₁ ∧ ¬f₂ ⊧ ⊥ -> ¬(f₁ ⇒ f₂) ⊧ ⊥.
Proof.
  intros f₁ f₂ h.
  unfold consequence,est_modele,equiv in *.
  simpl in *.
  intros v H0.
  specialize (h v).
  destruct (interp_def v f₁);destruct (interp_def v f₂);auto.
Qed.

Lemma tableau_nonOu : forall F f₁ f₂, ¬f₁ ∧ ¬f₂ ∧ F ⊧ ⊥ -> ¬(f₁ ∨ f₂) ∧ F ⊧ ⊥.
Proof.
  intros F f₁ f₂ h.
  unfold consequence,est_modele,equiv in *.
  simpl in *.
  intros v H0.
  specialize (h v).
  destruct (interp_def v f₁);destruct (interp_def v f₂);destruct (interp_def v F);auto.
Qed.


Lemma tableau_nonOu' : forall f₁ f₂, ¬f₁ ∧ ¬f₂ ⊧ ⊥ -> ¬(f₁ ∨ f₂) ⊧ ⊥.
Proof.
  intros f₁ f₂ h.
  unfold consequence,est_modele,equiv in *.
  simpl in *.
  intros v H0.
  specialize (h v).
  destruct (interp_def v f₁);destruct (interp_def v f₂);auto.
Qed.

Lemma tableau_ferme_branche : forall F f, (F ∧ f) ∧ ¬f ⊧ ⊥.
Proof.
  intros F f.
  red.
  intros v H.
  red in H.
  simpl in H.
  destruct (interp_def v F);destruct (interp_def v f).
  - discriminate H.
  - discriminate H.
  - discriminate H.
  - discriminate H.
Qed.

Lemma tableau_ferme_branche' : forall F f, f ∧ ¬f ∧ F ⊧ ⊥.
Proof.
  intros F f.
  setoid_rewrite Et_sym at 2.
  setoid_rewrite Et_assoc.
  setoid_rewrite Et_sym at 2.
  apply tableau_ferme_branche.
Qed.

Lemma tableau_ferme_branche'' : forall F f, (f ∧ ¬f) ∧ F ⊧ ⊥.
Proof.
  intros F f.
  setoid_rewrite <- Et_assoc.
  apply tableau_ferme_branche'.
Qed.

Lemma p_et_p_eq : forall p, p∧p ≡ p.
Proof.
  intros p.
  unfold equiv,consequence,est_modele.
  simpl.
  split.
  - intros v H.
    destruct (interp_def v p);auto.
  - intros v H.
    destruct (interp_def v p);auto.
Qed.

(* begin hide *)
(* Tactiques de preuve par tableaux *)

(* Une tactique pour extraire à gauche une formule de la
   conjonction. Utile pour pouvoir appliquer une des règles dessus
   ensuite. *)
Ltac extrait_ p :=
  match goal with
    | |- p ∧ _ ⊧ _ => idtac (* eviter que le rewrite ci-dessous echoue avec no progress *)
    | |- ?g ⊧ _ =>
      let sub_env := (eval compute in (extraction_disjuntion p g)) in
      match sub_env with
        | None => idtac
        | Some ?g' => rewrite (extraction_disjuntion_ok p g g');[|reflexivity]
      end
  end.

Local Tactic Notation "extrait" constr(p) := extrait_ p.

(* Une tactique par règle de tableau. Il y a un traitement particulier du cas où la formule est seule à gauche: on utilise un lemme (ex: tableau_Et') dédié. *)

Ltac do_Et p q := extrait (p∧q); apply tableau_Et.
Ltac do_nonEt p q := 
  first [apply (tableau_nonEt' p q) |
         extrait (¬(p∧q)); apply tableau_nonEt;split].
Ltac do_nonOu p q := 
  first [apply (tableau_nonOu' p q) |
         extrait (¬(p∨q)); apply tableau_nonOu].
Ltac do_Ou p q := 
  first [apply (tableau_Ou' p q) |
         extrait (p∨q); apply tableau_Ou;split].
Ltac do_Implique p q := 
  first [apply (tableau_implique' p q) |
         extrait (p⇒q); apply tableau_implique;split].
Ltac do_NonImplique p q :=
  first [apply (tableau_nonimplique' p q)  |
         extrait (¬(p⇒q)); apply tableau_nonimplique].
Ltac do_ferme p := extrait (¬p); extrait p; apply tableau_ferme_branche'.
(* end hide *)

(** ** Exemples d'application des tableaux. *)

Lemma conseq1: (X₁∨¬X₂) ∧ X₂ ⊧ X₁.
(* begin show *)
Proof.
  apply conseq_by_contradiction.
  do_Et (X₁ ∨ ¬X₂)  X₂.
  do_Ou X₁ (¬X₂).
  - do_ferme X₁.
  - do_ferme X₂.
Qed.


  Lemma conseq2 : (X₁ ∧ X₃ ) ∧ (¬X₁ ∨ X₂) ⊧ ⊥.
Proof.
  do_Ou (¬X₁) X₂.
  - do_ferme X₁.
  -
    (** Echec *)
Abort.

Lemma conseq3 : (¬ (X₁ ⇒ (X₂ ⇒ X₁))) ∧ ⊤ ⊧ ⊥.
Proof.
  do_NonImplique X₁ (X₂ ⇒ X₁).
  do_NonImplique X₂ X₁.
  do_ferme X₁.
Qed.

Lemma conseq4 : (¬ (X₁ ∨ X₂)) ∧ X₁ ⊧ ⊥.
Proof.
  do_nonOu X₁ X₂.
  do_ferme X₁.
Qed.

Lemma conseq5 : (¬ (X₁ ∧ X₂)) ∧ X₁ ∧ X₂ ⊧ ⊥.
Proof.
  do_nonEt X₁ X₂.
  - do_ferme X₁.
  - do_ferme X₂.
Qed.

Lemma conseq_exam_2014 : (¬X₂∨¬X₃) ⊧ (X₂ ∧ X₃) ⇒ X₁.
Proof.
  apply conseq_by_contradiction.
  do_NonImplique (X₂ ∧ X₃) (X₁).
  do_Et (X₂)(X₃).
  do_Ou (¬X₂) (¬X₃).
  - do_ferme X₂.
  - do_ferme X₃.
Qed.

Lemma conseq6 :  (X₁ ∨ X₂)∧(¬X₁ ∧ ¬X₂) ⊧ ⊥.
Proof.
 
    do_Ou  X₁ X₂.
    - do_ferme X₁. 
    - do_ferme X₂.
Qed.  

Lemma conseq7 :  ⊤  ⊧ (X₁ ⇒ (X₂ ⇒ X₃)) ⇒ ((X₁ ⇒ X₂) ⇒ (X₁ ⇒ X₃)).
  Proof.
  apply conseq_by_contradiction.
  do_NonImplique  (X₁ ⇒ (X₂ ⇒ X₃))  ((X₁ ⇒ X₂) ⇒ (X₁ ⇒ X₃)).
  do_Implique X₁ (X₂ ⇒ X₃).
  - do_NonImplique   (X₁ ⇒ X₂)  (X₁ ⇒ X₃).
    do_Implique X₁ X₂.   
    + do_NonImplique X₁ X₃.
      do_ferme X₁.
    + do_NonImplique X₁ X₃.
      do_ferme X₁.
  - do_NonImplique  (X₁ ⇒ X₂)  (X₁ ⇒ X₃).
    do_Implique X₁ X₂.
    + do_NonImplique X₁ X₃.
      do_ferme X₁.
    + do_Implique X₂ X₃.
       * do_ferme  X₂.
       * do_NonImplique  X₁ X₃.
         do_ferme X₃.
Qed.
         (* end show *)


  (* Faits utiles *)

Lemma Ou_comm: forall f₁ f₂, f₁ ∨ f₂  ≡ f₂ ∨ f₁.
Proof.
  intros f₁ f₂.
  split.
  - red;red;simpl.
    intros v H.
    red in H.
    simpl in H.
    destruct (interp_def v f₁); destruct (interp_def v f₂);try reflexivity.
    cbn in H.
    discriminate H.
  - red;red;simpl.
    intros v H.
    red in H.
    simpl in H.
    destruct (interp_def v f₁); destruct (interp_def v f₂);try reflexivity.
    cbn in H.
    discriminate H.
Qed.

Lemma Ou_assoc : forall f₁ f₂ f₃, f₁ ∨ (f₂ ∨ f₃) ≡ (f₁ ∨ f₂) ∨ f₃.
Proof.
  intros f₁ f₂ f₃.
  split.
  - repeat red; simpl.
    intros v H.
    red in H.
    simpl in H.
    destruct (interp_def v f₁); destruct (interp_def v f₂); destruct (interp_def v f₃); try assumption; try discriminate.
  - repeat red; simpl.
    intros v H.
    red in H.
    simpl in H.
    destruct (interp_def v f₁); destruct (interp_def v f₂); destruct (interp_def v f₃); try assumption; try discriminate.
Qed.


Lemma Ou_Faux: forall φ, ⊥ ∨ φ ≡ φ.
Proof.
  intros φ. 
  red.
  split.
  - red;intros.
    red in H.
    cbn in H.
    red.
    destruct (interp_def v φ);auto.
  - red;intros.
    red in H.
    red.
    cbn.
    destruct (interp_def v φ);auto.
Qed.

Lemma Ou_same: forall φ, φ ∨ φ ≡ φ.
Proof.
  intros φ. 
  red.
  split.
  - red;intros.
    red in H.
    cbn in H.
    red.
    destruct (interp_def v φ);auto.
  - red;intros.
    red in H.
    cbn in H.
    red.
    cbn.
    rewrite H.
    reflexivity.
Qed.
