(** remove printing -> *)
(** remove printing forall *)
(** remove printing exists *)
(** remove printing ~ *)
(** remove printing => *)
(** printing -> $\longrightarrow$ #&#10230;# *)
(*moche printing => $\longrightarrow$ #&#10233;# *)

(** %\chapter{Calcul propositionnel}%#<h1 class="libtitle">Calcul propositionnel</h1># *)

(** Ce module formalise la logique propositionnelle sans variable
   (calcul propositionnel). *)

Require Import Morphisms.
Require Import Setoid.
Require Import tables_de_verite.


(** * Les formules propositionnelles (sans variables) *)

(** ** Défintion des formules *)

(** Les formules sont définies (par induction) par la grammaire
    suivante. *)

Inductive formule : Type :=
| Vrai: formule
| Faux: formule
| Non: formule -> formule
| Ou: formule -> formule -> formule
| Et: formule -> formule -> formule
| Implique: formule -> formule -> formule.

(** ** Exemples de formule sans notation *)
(**
[
Check Vrai.
Check Faux.
Check (Ou Vrai Vrai).
Check (Ou Faux Vrai).
Check (Ou (Ou Vrai Faux) Vrai).
]
**)
(** ** Notations usuelles *)

(* begin hide *)
Local Reserved Notation  "X ∨ Y" (at level 85,right associativity).
Local Reserved Notation "X ∧ Y" (at level 82,right associativity).
Local Reserved Notation "¬ X" (at level 80).
Local Reserved Notation "X ⇒ Y" (at level 86,right associativity).
(* end hide *)
Local Notation "⊤":= Vrai.
Local Notation "⊥":= Faux.
Local Notation "¬ X":= (Non X).
Local Notation "X ∨ Y":= (Ou X Y).
Local Notation "X ∧ Y":= (Et X Y).
Local Notation "X ⇒ Y":= (Implique X Y).
(** ** Exemples avec les notations usuelles *)
(**
[
Check ⊤.
Check ⊥.
Check (⊤ ∨ ⊤).
Check (⊥ ∨ ⊤).
Check ((⊤ ∨ ⊥) ∨ ⊤).
Check (⊤ ∨ ⊥ ∨ ⊤).
Check (⊤ ∨ (⊥ ∨ ⊤)).
]
*)
(** * Interprétation d'une formule (Sémantique) *)

(** ** Définition de l'interprétation d'une formule *)

(** Définition de l'interprétation d'une formule: on applique les
    tables de vérité des feuilles jusqu'à la racine. *)
Function interp_def (f:formule) : bool :=
  match f with
    | ⊤ => table_Vrai
    | ⊥ => table_Faux
    | ¬ f => table_Non (interp_def f)
    | f₁ ∨ f₂ => table_Ou (interp_def f₁) (interp_def f₂)
    | f₁ ∧ f₂ => table_Et (interp_def f₁) (interp_def f₂)
    | f₁ ⇒ f₂ => table_Implique (interp_def f₁) (interp_def f₂)
  end.

(** [
Eval compute in interp_def (Implique ⊤ (Ou ⊤ ⊥)).
Eval compute in interp_def (Implique ⊤ (Ou ⊥ ⊥)). ] *)
(** Version "optimisée" qui n'évalue la sous-formule de
    droite que si nécessaire. *)
Function interp (f:formule) : bool :=
  match f with
    | ⊤ => true
    | ⊥ => false
    | ¬f => if interp f then false else true
    | f₁ ∨ f₂ => if interp f₁ then true else interp f₂
    | f₁ ∧ f₂ => if interp f₁ then interp f₂ else false
    | f₁ ⇒ f₂ => if interp f₁ then interp f₂ else true
  end.

(** [
Eval compute in interp (Implique ⊤ (Ou ⊤ ⊥)).
Eval compute in interp (Ou ⊥ ⊥). ] *)
(** Preuve de correction de la version optimisée. *)
Lemma interp_correct: forall f:formule, interp_def f = interp f.
Proof.
  induction f.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. repeat rewrite IHf.
    simpl. destruct (interp f);simpl;reflexivity.
  - simpl. repeat rewrite IHf1, IHf2.
    simpl. destruct (interp f2); destruct (interp f1);simpl;reflexivity.
  - simpl. repeat rewrite <- IHf1, <- IHf2.
    destruct (interp f2); destruct (interp f1);simpl;
    repeat rewrite IHf1, IHf2;simpl; reflexivity.
  - simpl. repeat rewrite IHf1, IHf2.
    simpl. destruct (interp f2); destruct (interp f1);simpl;reflexivity.
Qed.


(** * Preuves d'équivalences entre formules *)

(** Dans le calcul propositionnel deux formules sont équivalentes si
    leurs interprétations sont égales. Dans les logiques avec variables
    nous verrons que la notion d'équivalence fait intervenir la notion
    de _valuation_ des variables. *)

Local Notation "f ≡ g" := ((interp f) = (interp g)) (at level 180).

Lemma eq_implique : forall x y : formule, x ⇒ y ≡ ¬x ∨ y.
Proof.
  intros x y.
  cbn.
  destruct (interp x).
  - reflexivity.
  - reflexivity.
Qed.

Lemma eq_et : forall x y: formule, x ∧ y ≡ ¬(¬x ∨ ¬y).
Proof.
  intros x y.
  simpl.
  destruct (interp x).
  - destruct (interp y).
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma eq_not : ⊥ ≡ ¬⊤.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma eq_not2 : forall x : formule,    ¬x  ≡  x ⇒ ⊥ .
Proof.
  intros x.
  simpl.
  destruct (interp x).
  - reflexivity.
  - reflexivity.
Qed.

Lemma eq_ou : forall x y : formule,   x ∨ y  ≡  ¬x ⇒  y.
Proof.
  intros x y.
  simpl.
  destruct (interp x).
  - reflexivity.
  - reflexivity.
Qed.



(** * Réduction des connecteurs au sous-ensemble {⊤,¬,∨} *)

(** Les différents connecteurs correspondent à des constructions
    logiques essentiellement issues du langage naturel. En réalité ces
    constructions sont redondantes et un très petit nombre de
    connecteurs permet d'exprimer tous les autres. Par exemple on voit
    dans la suite que les trois connecteurs {⊤,¬,∨} peuvent être
    combinés pour remplacer tous les autres en utilisant les
    propriétés d'équivalence prouvées plus haut. *)


(** Définition de la propriété "être formé uniquement avec des ¬, ∨
      et ⊤". *)

Inductive is_reduced : formule -> Prop :=
  Vrai_is_red: is_reduced ⊤
| Non_is_red: forall f,is_reduced f -> is_reduced (¬ f)
| Or_is_red: forall f g,is_reduced f -> is_reduced g -> is_reduced (f ∨ g).


(** Fonction qui remplace les formules contenant les autres
    connecteurs par des formule réduites équivalentes. *)

Function reduce (f:formule) : formule :=
  match f with
    | ⊤ => ⊤
    | ⊥ => ¬ ⊤
    | ¬ f => ¬ (reduce f)
    | f₁ ∨ f₂ => (reduce f₁) ∨ (reduce f₂)
    | f₁ ∧ f₂ => ¬ (¬ (reduce f₁) ∨ ¬ (reduce f₂))
    | f₁ ⇒ f₂ => ¬ (reduce f₁) ∨ (reduce f₂)
  end.

(** la transformation est toujours équivalente. *)

Lemma reduce_correct: forall f:formule, f ≡ (reduce f).
Proof.
  induction f.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite IHf. reflexivity.
  - simpl. rewrite IHf1, IHf2. reflexivity.
  - simpl reduce. rewrite <- eq_et.
    simpl.  rewrite <- IHf1, <- IHf2. reflexivity.
  - simpl reduce. rewrite <- eq_implique.
    simpl. rewrite <- IHf1, <- IHf2. reflexivity.
Qed.


(** La transformation produit bien une formule réduite, c'est-à-dire ne
   contenant que les connecteurs {⊤,¬,∨}. *)

Lemma reduce_complete : forall f, is_reduced (reduce f).
Proof.
  induction f.
  - simpl. apply Vrai_is_red.
  - simpl. apply Non_is_red. apply Vrai_is_red.
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

(** cet ensemble de connecteur n'est pas unique; Par  exemple, on peut aussi se limiter aux connectuer  ⊥ et ⇒ . Comme le montre les lemme ci-dessous: *)

(** Définition de la propriété "être formé uniquement avec  ⊥ et ⇒ ". *)

Inductive is_reduced2 : formule -> Prop :=
  Faux_is_red2: is_reduced2 ⊥
| Implique_is_red2: forall f g,is_reduced2 f -> is_reduced2 g -> is_reduced2 (f  ⇒  g).


(** Fonction qui remplace les formules contenant les autres
    connecteurs par des formule réduites équivalentes. *)

Function reduce2 (f:formule) : formule :=
  match f with
    | ⊤ =>  ⊥ ⇒ ⊥
    | ⊥ =>  ⊥
    | ¬ f =>  (reduce2 f) ⇒ ⊥
    | f₁ ∨ f₂ => ((reduce2 f₁) ⇒ ⊥) ⇒ (reduce2 f₂)
    | f₁ ∧ f₂ => ((reduce2 f₁)  ⇒  ((reduce2 f₂)⇒ ⊥))⇒ ⊥
    | f₁ ⇒ f₂ =>  (reduce2 f₁)  ⇒  (reduce2 f₂)
  end.

(** la transformation est toujours équivalente. *)

Lemma reduce_correct2: forall f:formule, f ≡ (reduce2 f).
Proof.
  induction f.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite IHf. reflexivity.
  - simpl. rewrite <-IHf1,  <-IHf2. destruct (interp f1).
    + reflexivity.
    + reflexivity.
  - simpl reduce2. rewrite  eq_et. rewrite eq_not2.
    simpl.  rewrite <-IHf1,  <-IHf2. destruct (interp f1).
    +reflexivity.    
    +reflexivity.
  -  simpl. rewrite <- IHf1, <- IHf2. reflexivity.
Qed.


(** La transformation produit bien une formule réduite, c'est-à-dire ne
   contenant que les connecteurs {⊥ et ⇒}. *)

Lemma reduce_complete2 : forall f, is_reduced2 (reduce2 f).
Proof.
  induction f.
  - simpl. apply Implique_is_red2.
    + apply Faux_is_red2.
    + apply Faux_is_red2.
  - simpl. apply Faux_is_red2.
  - simpl. apply Implique_is_red2.
    + assumption.
    + apply Faux_is_red2.
  - simpl. apply Implique_is_red2.
    + apply Implique_is_red2.
      * assumption.
      * apply Faux_is_red2.
    + assumption.
  - simpl. apply Implique_is_red2.
    + apply Implique_is_red2.
      * assumption.
      * { apply Implique_is_red2.
         - assumption.
         - apply Faux_is_red2.
        }
    + apply Faux_is_red2.
  - simpl.  apply Implique_is_red2.
    + assumption.
    + assumption.
Qed.


