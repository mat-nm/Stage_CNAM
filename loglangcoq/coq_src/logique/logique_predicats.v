(* begin hide *)
(** remove printing -> *)
(** remove printing forall *)
(** remove printing exists *)
(** remove printing ~ *)
(** remove printing => *)
(** printing -> $\longrightarrow$ #&#10230;# *)
(*moche printing => $\longrightarrow$ #&#10233;# *)
(* end hide *)

(** %\chapter{Logique des prédicats sans quantificateurs}%
    #<h1 class="libtitle">Logique des prédicats sans quantificateur</h1># *)
(** Ce module formalise la logique des prédicats sans quantificateur.
    Les termes ne contiennent pas de symboles de fonctions, un terme
    est donc une variable. Les prédicats sont d'arité quelconque. *)
(* begin hide *)
From Stdlib Require Import Morphisms FunInd Setoid List ZArith.
Require Import MiscFacts tables_de_verite logique_generique.
Notation ℕ := nat.
(* end hide *)

(** * Les formules  *)

(** ** Les termes  *)

(** Le type des termes. Les termes ne sont que des variables. La
    logique propositionnelle inclut en principe les symboles de
    fonctions mais cela compliquerait la présentation. *)

Inductive terme: Type :=
| TVar: ℕ -> terme.

(** ** Les formules  *)

(** Le type des formules logique avec prédicats (sans symbole de
    fonction) et sans quantification. Les noms de prédicats sont
    représentés par des numéros, un prédicat prend un seul argument:
    une liste de termes. *)

Inductive formule : Type :=
| Vrai: formule
| Faux: formule
| Var: ℕ -> formule
| Non: formule -> formule
| Ou: formule -> formule -> formule
| Et: formule -> formule -> formule
| Implique: formule -> formule -> formule
| Pred: ℕ -> list terme -> formule.


(** *** Exemples de formules: *)

(* begin hide *)
(** [
Check Vrai.
Check Faux.
Check (Var 23).
Check (Ou Vrai Vrai).
Check (Ou Faux Vrai).
Check (Ou (Ou Vrai Faux) Vrai). ] *)
(* end hide *)

(** [
Check (Pred 1 (TVar 1::nil)). (** : formule *)
Check (Ou (Ou (Pred 1 (cons (TVar 1) (cons (TVar 2) nil))) Faux) Vrai).] *)


(** *** Notations usuelles *)

(* begin hide *)
Reserved Notation  "X ∨ Y" (at level 85,right associativity).
Reserved Notation "X ∧ Y" (at level 82,right associativity).
Reserved Notation "¬ X" (at level 80).
Reserved Notation "X ⇒ Y" (at level 86,right associativity).
(* end hide *)

Notation "⊤":= Vrai.
Notation "⊥":= Faux.
Notation "¬ X":= (Non X).
Notation "X ∨ Y":= (Ou X Y).
Notation "X ∧ Y":= (Et X Y).
Notation "X ⇒ Y":= (Implique X Y).

Notation "'X₁'":= (Var 1).
Notation "'X₂'":= (Var 2).
(* begin hide *)
Notation "'X₃'":= (Var 3).
Notation "'X₄'":= (Var 4).
Notation "'X₅'":= (Var 5).
Notation "'X₆'":= (Var 6).
Notation "'X₇'":= (Var 7).
Notation "'X₈'":= (Var 8).
Notation "'X₉'":= (Var 9).
Notation "'X₁₀'":= (Var 10).
(* end hide *)

Notation "'x₁'":= (TVar 1).
Notation "'x₂'":= (TVar 2).

(* begin hide *)
Notation "'x₃'":= (TVar 3).
Notation "'x₄'":= (TVar 4).
Notation "'x₅'":= (TVar 5).
Notation "'x₆'":= (TVar 6).
Notation "'x₇'":= (TVar 7).
Notation "'x₈'":= (TVar 8).
Notation "'x₉'":= (TVar 9).
Notation "'x₁₀'":= (TVar 10).
(* end hide *)

(* begin hide *)
Reserved Notation "'p₁' l" (at level 60).
Reserved Notation "'p₂' l" (at level 60).
Reserved Notation "'p₃' l" (at level 60).
Reserved Notation "'p₄' l" (at level 60).
Reserved Notation "'p₅' l" (at level 60).
Reserved Notation "'p₆' l" (at level 60).
Reserved Notation "'p₇' l" (at level 60).
Reserved Notation "'p₈' l" (at level 60).
(* end hide *)

Notation "'p₁' l":= (Pred 1 l).
Notation "'p₂' l":= (Pred 2 l).
(* begin hide *)
Notation "'p₃' l":= (Pred 3 l).
Notation "'p₄' l":= (Pred 4 l).
Notation "'p₅' l":= (Pred 5 l).
Notation "'p₆' l":= (Pred 6 l).
Notation "'p₇' l":= (Pred 7 l).
Notation "'p₈' l":= (Pred 8 l).
(* end hide *)

(* begin hide *)
Reserved Notation "'[' x ',' .. ',' y ']'"
    (at level 0, format "'[  ' [ '/' x ',' .. ',' y ] ']'").

Global Notation "'[' x ',' .. ',' y ']'" := (cons x .. (cons y nil) ..).
(* end hide *)


(** *** Exemples avec notations *)

(* **** formules: *)
(** [
Check (Var 7).
Check X₇.
Check (Pred 1 (x₁::nil)).
Check (p₁ [x₁ , x₂ , x₃]).
Check (p₁ [x₁ , x₂ , x₃]).
] *)

(** **** termes: *)

(** [
Check x₇.
] *)

Scheme Equality for terme.

(** Décision de l'égalité sur les formules *)
Function formule_beq (φ ψ:formule)  {struct φ}: bool := 
  match φ,ψ with 
    | ⊤,⊤ => true
    | ⊥,⊥ => true
    | Var p,Var q => Nat.eqb p q
    |  φ₁ ⇒ φ₂, ψ₁ ⇒ ψ₂ => formule_beq φ₁ ψ₁ && formule_beq φ₂ ψ₂
    | φ₁ ∧ φ₂,ψ₁ ∧ ψ₂ => formule_beq φ₁ ψ₁ && formule_beq φ₂ ψ₂
    | φ₁ ∨ φ₂,ψ₁ ∨ ψ₂ => formule_beq φ₁ ψ₁ && formule_beq φ₂ ψ₂
    | ¬φ,¬ψ => formule_beq φ ψ
    | (Pred n1 l1) , (Pred n2 l2) => Nat.eqb n1 n2 &&
                                     forallb2 terme_beq l1 l2
    | _,_ => false
  end.

(* Correction de la décision *)
Lemma terme_eq_ok : forall t1 t2:terme, terme_beq t1 t2 = true <-> t1 = t2.
Proof.
  intros t1 t2.
  split; intro H.
  - destruct t1;destruct t2.
    destruct (eq_nat_dec n n0);auto.
    simpl in H.
    rewrite (internal_nat_dec_bl n n0 H).
    reflexivity.
  - subst.
    destruct t2;simpl;auto.
    induction n;simpl;auto.
Qed.

(* Corollaire: Forall2 sur terme_beq=true se ramène à Forall2 sur eq *)
Lemma terme_eq_true_eq_iff: forall l1 l2,
              Forall2 (fun x y : terme => terme_beq x y = true) l1 l2
              <-> Forall2 Logic.eq l1 l2.
Proof.
  induction l1;simpl;intros.
  - destruct l2;simpl;auto.
    + split;intros.
      * constructor.
      * constructor.
    + split;intros.
      * inversion H.
      * inversion H.
  - destruct l2;simpl;auto.
    + split;intros.
      * inversion H.
      * inversion H.
    + split;intros.
      * { constructor.
          - inversion H;subst;auto.
            apply terme_eq_ok;assumption. 
          - inversion H;subst.
            apply IHl1.
            assumption. }
      * { constructor.
          - inversion H;subst;auto.
            apply terme_eq_ok.
            reflexivity.
          - inversion H;subst.
            apply IHl1.
            assumption. }
Qed.


Lemma formule_eq_okr : forall φ ψ:formule, formule_beq φ ψ = true -> φ = ψ.
Proof.
  intros φ ψ H.
  functional induction formule_beq φ ψ;auto.
  - rewrite Nat.eqb_eq in H;subst;auto.
  - apply Bool.andb_true_iff in H.
    destruct H.
    rewrite IHb,IHb0;auto.
  - apply Bool.andb_true_iff in H.
    destruct H.
    rewrite IHb,IHb0;auto.
  - apply Bool.andb_true_iff in H.
    destruct H.
    rewrite IHb,IHb0;auto.
  - rewrite IHb;auto.
  - apply Bool.andb_true_iff in H.
    destruct H.
    rewrite Nat.eqb_eq in H;subst;auto.
    apply Forall2_forallb2_iff in H0.
    apply f_equal2;auto.
    rewrite terme_eq_true_eq_iff in H0.
    apply Forall2_eq_eq_iff.
    assumption.
  - discriminate.
Qed.

Lemma formule_eq_okl : forall φ ψ:formule, φ = ψ -> formule_beq φ ψ = true.
Proof.
  intros φ ψ H.
  subst.
  induction ψ;simpl;subst;auto.
  - rewrite Nat.eqb_refl.
    reflexivity.
  - rewrite IHψ1.
    rewrite IHψ2.
    reflexivity.
  - rewrite IHψ1.
    rewrite IHψ2.
    reflexivity.
  - rewrite IHψ1.
    rewrite IHψ2.
    reflexivity.
  - rewrite Nat.eqb_refl.
    simpl.
    apply Forall2_forallb2_iff.
    apply terme_eq_true_eq_iff.
    apply Forall2_eq_eq_iff.
    reflexivity.
Qed.

Lemma formule_eq_ok : forall φ ψ:formule, φ = ψ <-> formule_beq φ ψ = true.
Proof.
  intros φ ψ.
  split;intros.
  apply formule_eq_okl;auto.
  apply formule_eq_okr;auto.
Qed.

Lemma formule_neq_ok : forall φ ψ:formule, φ <> ψ <-> formule_beq φ ψ = false.
Proof.
  intros φ ψ.
  split;intros.
  - destruct (formule_beq φ ψ) eqn:heq;auto.
    apply formule_eq_ok in heq.
    subst.
    elim H;auto.
  - intro abs;subst.
    rewrite -> (formule_eq_okl ψ ψ) in H.
    + discriminate.
    + reflexivity.
Qed.

Lemma formule_eq_dec : forall f1 f2: formule, {f1 = f2} + {f1<>f2}.
Proof.
  intros f1 f2.
  destruct (formule_beq f1 f2) eqn:heq.
  - left.
    eapply formule_eq_ok.
    assumption.
  - right.
    apply formule_neq_ok.
    assumption.
Qed.

(** Pour définir l'interprétation d'une formule nous avons de trois
    fonctions de valuation: celle pour les propositions (comme pour la
    logique propositionnelle avec variables), celle pour les termes et
    celle pour les prédicats. Les prédicats ont leur valeur dans les
    fonctions n-aires (DxD..xD -> bool). En effet u prédicat p à deux
    argument doit s'interpréter vers une fonction prenant deux entiers
    et retournant un booléen. Par exemple le prédicat "<" prend deux
    entier et retourne [true] si le premier est plus petit que le
    deuxième. *)

Definition val_propositions :=(nat -> bool).
Definition val_termes D :=(terme -> D).
Definition val_predicat D :=nat -> (list D -> bool).

(* L'interprétation d'une formule nécessite donc un triplet: *)

Record Valuation (D:Type) :=
  { predicats: val_predicat D;
    termes: val_termes D;
    propositions: val_propositions }.

(* begin hide *)
(* On montre l'argument de Valuation temporairement ici, pour la
pédagogie *)
Arguments Valuation D: clear implicits.
Arguments predicats [D] _ _ _.
Arguments termes [D] _ _.
Arguments propositions {D} _ _.
(* end hide *)

(** Définition de l'interprétation d'une formule: on applique les
    tables de vérité des feuilles jusqu'à la racine. *)

Function interp_def (v:Valuation Z) (f:formule) : bool :=
  match f with
    | ⊤ => table_Vrai
    | ⊥ => table_Faux
    | Var i => (v.(propositions) i)
    | Pred i l => (v.(predicats) i) (map v.(termes) l)
    | ¬ f => table_Non (interp_def v f)
    | f₁ ∨ f₂ => table_Ou (interp_def v f₁) (interp_def v f₂)
    | f₁ ∧ f₂ => table_Et (interp_def v f₁) (interp_def v f₂)
    | f₁ ⇒ f₂ => table_Implique (interp_def v f₁) (interp_def v f₂)
  end.

(* + Version "optimisée" qui n'évalue la sous-formule de droite que si
   nécessaire?  *)
(** On utilisera l'abus de notation suivant: [I[f]] à la place de
    [(interp_def I f)]. Attention toutefois à garder en mémoire qu'une
    interprétation I ne s'applique pas à une formule mais à une
    variable, c'est la fonction [interp_def] qui permet de généraliser
    une interprétation aux formules. Par ailleurs dans la suite par
    souci de clarté on écrira en général [Valuation] plutôt que
    [Valuation Z]. *)
Arguments Valuation {D}.
Notation "v [ f ]" := (interp_def v f) (at level 50).




Module Exemples.
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

  Definition is_zero l := 
    match l with
      | 0%Z::_ => true
      | _ => false
    end.

  Definition vp (n:nat): (list Z -> bool) :=
    match n with
      | 1 => is_zero
      | _ => (fun _ => false)
    end.

  Definition vt trm :=
    match trm with
      | TVar i => (0)%Z
    end.

  Definition III:Valuation := {| predicats:=vp; termes:=vt; propositions:=v₁|}.
  Definition III':Valuation := {| predicats:=vp; termes:=vt; propositions:=v₂|}.

(** [
  Eval compute in interp_def III (Implique ⊤ (Ou ⊤ ⊥)).
  Eval compute in interp_def III' (Implique ⊤ (Ou ⊤ ⊥)).
  Eval compute in interp_def III (Implique ⊤ (Ou ⊥ ⊥)).
  Eval compute in interp_def III' (p₁[x₁]).
  Eval compute in interp_def III' (Implique (p₁[x₁]) ⊥).
  Eval compute in interp_def III' (Implique (p₁[x₁]) (Ou ⊥ ⊥)).
] *)

End Exemples.

(** * Conséquence, modèle etc *)

(** On applique les définitions de conséquence, modèle etc du
    chapitre #<a href="logique_generique.html">logique_generique</a>#
    avec les notions de valuation et d'interprétation ci-dessous. *)

(* begin hide *)
Module LogPredVar<: Logique.
  Definition formule := formule.
  Definition t := formule.
  Definition eq := @Logic.eq formule.
  Lemma eq_refl : forall x : t, eq x x.
  Proof.
    intros x.
    apply @eq_refl.
  Qed.
  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    intros x y.
    apply @eq_sym.
  Qed.
  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    intros x y z.
    apply @eq_trans.
  Qed.

      
  Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    exact formule_eq_dec.
  Defined.
  (* end hide *)

  Definition valuation: Type:= @Valuation Z.
  Definition interpretation: valuation -> formule -> bool -> Prop :=
    fun v f b => interp_def v f = b.

  (* begin hide *)
  Lemma interpretation_unique:
    forall v f b1 b2, interpretation v f b1 -> interpretation v f b2 -> b1= b2.
  Proof.
    intros v f b1 b2 H H0.
    unfold interpretation in *.
    subst;reflexivity.
  Qed.
  (* end hide *)

  (** Résultat supplémentaire: l'interprétation est décidable (ce ne
      ser pas le cas pour la logique des prédicats avec
      quantificateurs *)
  Lemma interpretation_dec : forall v f,
                               interpretation v f true \/ interpretation v f false.
  Proof.
    intros v f.
    unfold interpretation.
    destruct (interp_def v f);simpl;auto.
  Qed.
(* begin hide *)
End LogPredVar.
(* end hide *)

(* begin hide *)
Import LogPredVar.
(* Module LogPredVarDefs:=LogiqueDefs(LogPredVar).  *)
Module Import LogPredVarEnv:=Environnement(LogPredVar). 
Import LogPredVarEnv.DEFS.
(* Open Scope logique_scope. *)

Ltac smpl := unfold interpretation, equiv, consequence, est_modele in *;simpl in *.
Tactic Notation "smpl*" := repeat progress smpl.
(* end hide *)

(** Une autre définition pour l'équivalence: l'interprétation des deux
    formules est toujours identique.  *)
(* QUESTION: est-ce toujours vrai, en particulier lorsque
   l'interprétation n'est plus décidable. *)
Definition equivalent p1 p2 :=
  forall v b, (interpretation v p1 b)<->(interpretation v p2 b).

(** Preuve d'equivalence entre equiv et equivalence. *)

Lemma equivEquivalence :forall p1 p2,(DEFS.equiv p1 p2) <-> (equivalent p1 p2).
  intros p1 p2.
  unfold equivalent.
  smpl*.
  split.
  - intros [h1 h2] v.
    specialize (h1 v).
    specialize (h2 v).
    destruct (interp_def v p2);destruct (interp_def v p1);simpl;intros;auto;try reflexivity;try now discriminate.
    + discriminate h2;reflexivity.
    + discriminate h1;reflexivity.
  - intros h.
    split; intros v h'.
    + apply h;assumption.
    + apply h;assumption.
Qed.

 

Module Exemples_modeles.
 (* Dansla trunk j'aimerais faire Recursive Arguments interpretation 1
    pour dire à simpl de déplier interpretation. *)
  Lemma modele1 : forall v n, ⊧[v] (Var n) ∨ ¬ (Var n).
  Proof.
    intros v n.
    red.
    smpl.
    destruct (propositions v n);simpl.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma modele2 : forall v, ⊧[v] (X₁ ∨ ¬ X₂) ∨ X₂.
  Proof.
    intros v.
    red.
    smpl.
    destruct (v.(propositions) 1).
    - destruct (v.(propositions) 2).
      + reflexivity.
      + reflexivity.
    - destruct (v.(propositions) 2).
      + reflexivity.
      + reflexivity.
  Qed.

End Exemples_modeles.


Module Exemples_conseq.
  Lemma conseq1: (X₁∨¬X₂) ∧ X₂ ⊧ X₁.
  Proof.
    repeat red.
    smpl*.
    intros v H.
    simpl in *.
    destruct (propositions v 1).
    - reflexivity.
    - destruct (propositions v 2).
      + discriminate H.
      + discriminate H.
  Qed.

End Exemples_conseq.

(** * Preuves d'équivalences entre formules *)

Lemma eq_implique : forall x y : formule, x ⇒ y ≡ ¬x ∨ y.
Proof.
  intros x y.
  smpl*.
  split;intros.
  - functional inversion H;subst;clear H;simpl.
    + reflexivity.
    + destruct (interp_def v y);reflexivity.
  - destruct (interp_def v x);simpl in *.
    + assumption.
    + reflexivity.
Qed.

Lemma eq_et : forall x y: formule, (x ∧ y) ≡ ¬ (¬x ∨ ¬y).
Proof.
  intros x y.
  smpl*.
  split;intros.
  - destruct (interp_def v x).
    + destruct (interp_def v y).
      * reflexivity.
      * discriminate.
    + simpl in H. destruct (interp_def v y); discriminate.
  - destruct (interp_def v x).
    + destruct (interp_def v y).
      * reflexivity.
      * discriminate.
    + destruct (interp_def v y);discriminate.
Qed.

Lemma eq_not : ⊥ ≡ ¬ ⊤.
Proof.
  simpl.
  unfold equiv,consequence,est_modele. simpl.
  split;intros.
  - discriminate.
  - discriminate.
Qed.

(* begin hide *)

Lemma equiv_refl: forall f, f ≡ f.
Proof.
  split;red;auto.
Qed.

Lemma equiv_sym: forall f₁ f₂, (f₁ ≡ f₂) -> (f₂ ≡ f₁).
Proof.
  split;red;intros;red in H;destruct H;auto.
Qed.

Lemma equiv_trans: forall f₁ f₂ f₃, (f₁ ≡ f₂) -> (f₂ ≡ f₃) -> (f₁ ≡ f₃).
Proof.
  unfold equiv, consequence, est_modele in *.
  intros f₁ f₂ f₃ H H0.
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
  smpl*.
  destruct 1.
  specialize (H v).
  specialize (H0 v).
  destruct (interp_def v x);destruct (interp_def v y0);try reflexivity;auto.
  symmetry;auto.
Qed.


Add Parametric Morphism: Et
    with signature equiv ==> equiv ==> equiv as and_morphism.
Proof.
  intros x y H x0 y0 H0.
  smpl*.
  split.
  - intros v H1.
    destruct H as [H' H''].
    destruct H0 as [H0' H0''].
    destruct (interp_def v x) eqn:heq;destruct (interp_def v x0) eqn:heq';auto.
    + rewrite H'.
      * simpl.
        { rewrite H0'.
          - reflexivity.
          - assumption. }
      * assumption.
    + discriminate.
    + discriminate.
    + discriminate.
  - intros v H1.
    destruct H as [H' H''].
    destruct H0 as [H0' H0''].
    destruct (interp_def  v y) eqn:heq;destruct (interp_def v y0) eqn:heq';auto.
    + rewrite H''.
      * { rewrite H0''.
          - reflexivity. 
          - assumption. }
      * assumption.
    + discriminate.
    + discriminate.
    + discriminate.
Qed.

Add Parametric Morphism: Ou
    with signature equiv ==> equiv ==> equiv as Ou_morphism.
Proof.
  intros x y H x0 y0 H0.
  smpl*.
  split.
  - intros v H1.
    destruct H as [H' H''].
    destruct H0 as [H0' H0''].
    destruct (interp_def v x) eqn:heq;destruct (interp_def v x0) eqn:heq';auto.
    + rewrite H'. rewrite H0'.
      * reflexivity. 
      * assumption.
      * assumption.
    + rewrite H'. destruct (interp_def v y0);auto.
      assumption.
    + destruct (interp_def v y ) eqn:heq''.
      *   destruct (interp_def v y0);auto.
      * rewrite H0';auto.
    + simpl in H1. discriminate H1.
  - intros v H1.
    destruct H as [H' H''].
    destruct H0 as [H0' H0''].
    destruct (interp_def v x) eqn:heq;destruct (interp_def v x0) eqn:heq';auto.
    + destruct (interp_def v y ) eqn:heq''.
      * { assert (interp_def v x =  true).
          - apply H''. assumption.
          - rewrite H in heq;discriminate. }
      * { assert (interp_def v x0 =  true).
          - apply H0''.
            destruct (interp_def v y0).
            + reflexivity.
            + discriminate H1.
          - rewrite H in heq';discriminate. }
Qed.


Add Parametric Morphism: Non
    with signature equiv ==> equiv as Non_morphism.
Proof.
  intros x y H.
  smpl*.
  split.
  - intros v H1.
    destruct H as [H' H''].
    destruct (interp_def v x) eqn:heq.
    + discriminate.
    + destruct (interp_def v y) eqn:heq''.
      * assert (interp_def v x = true).
        { apply  H''. assumption. }
        rewrite H in heq; discriminate.
      * reflexivity.
  - intros v H1.
    destruct H as [H' H''].
    destruct (interp_def v y) eqn:heq.
    + discriminate.
    + destruct (interp_def v x) eqn:heq''.
      * assert (interp_def v y = true).
        { apply  H'. assumption. }
        rewrite H in heq; discriminate.
      * reflexivity.
Qed.

Add Parametric Morphism: est_modele
    with signature Logic.eq ==> equiv ==> iff as estmodele_morphism.
Proof.
  intros v x y H.
  red in H.
  red.
  destruct H as [h h'].
  unfold consequence,est_modele,equiv in *.
  split;intro h''.
  auto.
  auto.
Qed.

Add Parametric Morphism: consequence
    with signature equiv ==> equiv ==> iff as conseq_morphism.
Proof.
  intros x y H x' y' H0.
  red in H,H0.
  red.
  destruct H as [h h'].
  destruct H0 as [h'' h'''].
  unfold consequence,est_modele,equiv in *.
  split.
  - intros H v H0.
    auto.
  - auto.
Qed.

(* end hide *)

(** * Preuve par réfutation (Utile pour la preuve par tableau plus loin).  *)

Lemma conseq_by_contradiction': forall f₁ f₂: formule, f₁ ⊧ f₂ -> f₁ ∧ ¬f₂ ⊧ ⊥.
Proof.
  intros f₁ f₂.
  smpl*.
  intros H v H0.
  simpl in H0.
  destruct (interp_def v f₁) eqn:heq.
  - assert (heq':interp_def v f₂ = true).
    { apply H. apply heq. }
    rewrite heq' in H0.
    discriminate H0.
  - simpl in H0.
    destruct (interp_def v f₂) ; discriminate.
Qed.

(** Pour prouver f ⊧ g on peut prouver f ∧ ¬g ⊧ ⊥ .  *)

Lemma conseq_by_contradiction: forall f₁ f₂: formule,  ¬f₂ ∧ f₁ ⊧ ⊥ -> f₁ ⊧ f₂.
Proof.
  intros f₁ f₂.
  smpl*.
  intros H v heq.
  specialize (H v).
  rewrite heq in H.
  destruct (interp_def v f₂) eqn:heq'.
  - reflexivity.
  - discriminate H. reflexivity.
Qed.

(** * Preuve par la méthode des tableaux  *)

(** ** Lemmes auxilaires  *)

Lemma and_affaiblissement_conseq : forall v f₁ f₂, ⊧[v] f₁∧f₂ -> ⊧[v]f₁.
Proof.
  intros v f₁ f₂ H.
  smpl*.
  destruct (interp_def v f₁).
  - reflexivity.
  - simpl in H. destruct (interp_def v f₂);discriminate H.
Qed.

Lemma and_affaiblissement_contr : forall f₁ f₂, f₁ ⊧ ⊥ -> f₁∧f₂ ⊧ ⊥ .
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
  smpl*.
  split;intros.
  - destruct (interp_def v f₁).
    + destruct (interp_def v f₂).
      * assumption.
      * discriminate H.
    + simpl in H. destruct (interp_def v f₂); discriminate H.
  - destruct (interp_def v f₁).
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
  smpl*.
  split.
  - intros v H.
    destruct (interp_def v f₁); destruct (interp_def v f₂); destruct (interp_def v f₃); try assumption; try discriminate.
  - intros v H.
    destruct (interp_def v f₁); destruct (interp_def v f₂); destruct (interp_def v f₃); try assumption; try discriminate.
Qed.


Function extraction_disjuntion (f F: formule): option formule :=
  match F with
    | g ∧ F' =>
      if formule_beq f g then Some F'
      else
        if formule_beq f F' then Some g (* comme ça pas de true à mettre à la fin *)
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
Eval compute in (extraction_disjuntion  ((X₁ ∨ ¬X₂) ∧ X₂) (((X₁ ∨ ¬X₂) ∧ X₂) ∧ ¬X₁)).
] *)


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
  - apply formule_eq_ok in e0.
    inversion H;subst;reflexivity.
  - apply formule_eq_ok in e1.
    inversion H;clear H.
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

Lemma tableau_Ou : forall F f₁ f₂,
                     (f₁  ∧ F ⊧ ⊥)
                     /\ (f₂ ∧ F ⊧ ⊥)
                     -> (f₁ ∨ f₂) ∧ F ⊧ ⊥.
Proof.
  intros F f₁ f₂ H.
  smpl*.
  destruct H as [h h'].
  intros v H0.
  specialize (h v).
  specialize (h' v).
  apply h.
  simpl in *.
  destruct (interp_def v f₁);destruct (interp_def v f₂);simpl in *;
  destruct (interp_def v F);auto.
Qed.


Lemma tableau_Ou' : forall f₁ f₂,
                     (f₁ ⊧ ⊥)
                     /\ (f₂ ⊧ ⊥)
                     -> (f₁ ∨ f₂) ⊧ ⊥.
Proof.
  intros f₁ f₂ H.
  smpl*.
  destruct H as [h h'].
  intros v H0.
  specialize (h v).
  specialize (h' v).
  apply h.
  simpl in *.
  destruct (interp_def v f₁);destruct (interp_def v f₂);simpl in *;auto.
Qed.

Lemma tableau_nonEt : forall F f₁ f₂,
                        (¬f₁ ∧ F ⊧ ⊥) /\ (¬f₂ ∧ F ⊧ ⊥)
                        -> ¬(f₁ ∧ f₂) ∧ F ⊧ ⊥.
Proof.
  intros F f₁ f₂ H.
  smpl*.
  destruct H as [h h'].
  intros v H0.
  specialize (h v).
  specialize (h' v).
  apply h.
  simpl in *.
  destruct (interp_def v f₁);destruct (interp_def v f₂);simpl in *;
  destruct (interp_def v F);auto.
Qed.

Lemma tableau_nonEt' : forall f₁ f₂,
                        (¬f₁ ⊧ ⊥) /\ (¬f₂ ⊧ ⊥)
                        -> ¬(f₁ ∧ f₂) ⊧ ⊥.
Proof.
  intros f₁ f₂ H.
  smpl*.
  destruct H as [h h'].
  intros v H0.
  specialize (h v).
  specialize (h' v).
  apply h.
  simpl in *.
  destruct (interp_def v f₁);destruct (interp_def v f₂);simpl in *;auto.
Qed.


Lemma tableau_implique : forall F f₁ f₂,
                           (¬f₁ ∧ F ⊧ ⊥) /\ (f₂ ∧ F ⊧ ⊥)
                           -> (f₁ ⇒ f₂) ∧ F ⊧ ⊥.
Proof.
  intros F f₁ f₂ H.
  smpl*.
  destruct H as [h h'].
  intros v H0.
  specialize (h v).
  specialize (h' v).
  apply h.
  simpl in *.
  destruct (interp_def v f₁);destruct (interp_def v f₂);destruct (interp_def v F);auto.
Qed.

Lemma tableau_implique' : forall f₁ f₂,
                           (¬f₁ ⊧ ⊥) /\ (f₂ ⊧ ⊥)
                           -> (f₁ ⇒ f₂) ⊧ ⊥.
Proof.
  intros f₁ f₂ H.
  smpl*.
  destruct H as [h h'].
  intros v H0.
  specialize (h v).
  specialize (h' v).
  apply h.
  simpl in *.
  destruct (interp_def v f₁);destruct (interp_def v f₂);auto.
Qed.


Lemma tableau_Et : forall F f₁ f₂, f₁ ∧ f₂ ∧ F ⊧ ⊥ -> (f₁ ∧ f₂) ∧ F ⊧ ⊥.
Proof.
  intros F f₁ f₂ h.
  smpl*.
  intros v H0.
  specialize (h v).
  destruct (interp_def v f₁);destruct (interp_def v f₂);destruct (interp_def v F);auto.
Qed.

Lemma tableau_Et' : forall f₁ f₂, f₁ ∧ f₂ ⊧ ⊥ -> (f₁ ∧ f₂) ⊧ ⊥.
Proof.
  intros f₁ f₂ h.
  smpl*.
  intros v H0.
  specialize (h v).
  destruct (interp_def v f₁);destruct (interp_def v f₂);auto.
Qed.

Lemma tableau_nonimplique : forall F f₁ f₂, f₁ ∧ ¬f₂ ∧ F ⊧ ⊥ -> ¬(f₁ ⇒ f₂) ∧ F ⊧ ⊥.
Proof.
  intros F f₁ f₂ h.
  smpl*.
  intros v H0.
  specialize (h v).
  destruct (interp_def v f₁);destruct (interp_def v f₂);destruct (interp_def v F);auto.
Qed.


Lemma tableau_nonimplique' : forall f₁ f₂, f₁ ∧ ¬f₂ ⊧ ⊥ -> ¬(f₁ ⇒ f₂) ⊧ ⊥.
Proof.
  intros f₁ f₂ h.
  smpl*.
  intros v H0.
  specialize (h v).
  destruct (interp_def v f₁);destruct (interp_def v f₂);auto.
Qed.

Lemma tableau_nonOu : forall F f₁ f₂, ¬f₁ ∧ ¬f₂ ∧ F ⊧ ⊥ -> ¬(f₁ ∨ f₂) ∧ F ⊧ ⊥.
Proof.
  intros F f₁ f₂ h.
  smpl*.
  intros v H0.
  specialize (h v).
  destruct (interp_def v f₁);destruct (interp_def v f₂);destruct (interp_def v F);auto.
Qed.

Lemma tableau_nonOu' : forall f₁ f₂, ¬f₁ ∧ ¬f₂ ⊧ ⊥ -> ¬(f₁ ∨ f₂) ⊧ ⊥.
Proof.
  intros f₁ f₂ h.
  smpl*.
  intros v H0.
  specialize (h v).
  destruct (interp_def v f₁);destruct (interp_def v f₂);auto.
Qed.

Lemma tableau_ferme_branche : forall F f, (F ∧ f) ∧ ¬f ⊧ ⊥.
Proof.
  intros F f v H.
  smpl*.
  destruct (interp_def v F);destruct (interp_def v f);discriminate.
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


Lemma tableau_ferme_branche''' : forall f, f ∧ ¬f ⊧ ⊥.
Proof.
  intros f.
  intros.
  intros v h.
  unfold consequence,est_modele,equiv in *.
  smpl*.
  destruct (interp_def v f);discriminate.
Qed.

Lemma p_et_p_eq : forall a, a∧a ≡ a.
Proof.
  intros a.
  unfold equiv,consequence,est_modele.
  simpl.
  split.
  - intros v H.
    destruct (interp_def v a);auto.
  - intros v H.
    destruct (interp_def v a);auto.
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

Tactic Notation "extrait" constr(p) := extrait_ p.

(* Une tactique par règle de tableau. Il y a un traitement particulier du cas où la formule est seule à gauche: on utilise un lemme (ex: tableau_Et') dédié. *)

Ltac do_Et p q :=
  first [apply (tableau_Et' p q) |
         extrait (p∧q); apply tableau_Et].
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

(* begin show *)
(** ** Exemples d'application des tableaux. *)
Module Exemple_Tableaux.

Lemma conseq1: (X₁∨¬X₂) ∧ X₂ ⊧ X₁.
Proof.
  apply conseq_by_contradiction.
  do_Ou X₁ (¬X₂).
  - do_ferme X₁.
  - do_ferme X₂.
Qed.

Lemma conseq2 : (X₁ ∧ X₃ ) ∧ (¬X₁ ∨ X₂) ⊧ ⊥.
Proof.
  do_Et X₁ X₃.
  do_Ou (¬X₁) X₂.
  - do_ferme X₁.
  - (* Echec *)
Abort.

Lemma conseq3 : (¬ (X₁ ⇒ (X₂ ⇒ X₁))) ⊧ ⊥.
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

Lemma conseq5' : (¬ ((p₂((TVar 1::nil)) ) ∧ X₂)) ∧ (p₂((TVar 1::nil)) ) ∧ X₂ ⊧ ⊥.
Proof.
  do_nonEt (p₂((TVar 1::nil)) ) X₂.
  - do_ferme (p₂((TVar 1::nil)) ).
  - do_ferme X₂.
Qed.


Lemma conseq6 : (X₁ ∧ (p₂((TVar 1::nil)) ) ) ∧ (¬X₁ ∨ X₂) ⊧ ⊥.
Proof.
  do_Ou (¬X₁) X₂.
  - do_ferme X₁.
  - (* Echec *)
Abort.

End Exemple_Tableaux.
(* end show *)

