(* begin hide *)
(** remove printing -> *)
(** remove printing forall *)
(** remove printing exists *)
(** remove printing ~ *)
(** remove printing => *)
(** printing -> $\longrightarrow$ #&#10230;# *)
(*moche printing => $\longrightarrow$ #&#10233;# *)
(* end hide *)

(** %\chapter{Logique des prédicats avec quantificateurs (sans fonction)}%
    #<h1 class="libtitle">Logique des prédicats avec quantificateur (sans fonction)</h1># *)

(** Ce module formalise la logique des prédicats avec quantificateurs,
    les prédicats sont n-aires (nombre quelconque d'arguments) mais
    les termes (arguments des prédicats) ne contiennent pas de
    symboles de fonctions: ce sont uniquement des variables. *)

(* begin hide *)
From Stdlib Require Import Morphisms FunInd Setoid Lia List ZArith.
Require Import MiscFacts tables_de_verite logique_generique.
(* end hide *)

(** * Les formules  *)

(** ** Les termes  *)

(** Les termes ne sont que des variables. La logique propositionnelle
    inclut en principe les symboles de fonctions mais cela
    compliquerait la présentation. *)

Inductive terme: Type :=
| TVar: ℕ -> terme.

(** *** Exemples de termes *)

(* [
Check (TVar 7). (** : terme *)
] *)

(** ** Les formules  *)

(** Le type des formules logique avec prédicats (sans symbole de
    fonction) avec quantificateur. Les noms de prédicats sont
    représentés par des numéros, un prédicat prend un seul argument:
    une liste de termes. Les quantificateurs prennent en argument le
    numéro de la variable quantifiée. *)

Inductive formule : Type :=
| Vrai: formule
| Faux: formule
| Var: ℕ -> formule
| Non: formule -> formule
| Ou: formule -> formule -> formule
| Et: formule -> formule -> formule
| Implique: formule -> formule -> formule
| Pred: ℕ -> list terme -> formule
| FORALL: ℕ -> formule -> formule
| EXIST: ℕ -> formule -> formule.

(** *** Exemples de formules *)
(* begin hide *)
(** [
Check Vrai.
Check Faux.
Check (Var 23).
Check (Ou Vrai Vrai).
Check (Ou Faux Vrai).
Check (Ou (Ou Vrai Faux) Vrai).
(* end hide *)
Check (Pred 1 (TVar 1::nil)). (** : formule *)
Check (Ou (Ou (Pred 1 (cons (TVar 1) (cons (TVar 2) nil))) Faux) Vrai).
Check (FORALL 1 (Ou (Ou (Pred 1 (cons (TVar 1) (cons (TVar 2) nil))) Faux) Vrai)).
Check (EXIST 1 (Ou (Ou (Pred 1 (cons (TVar 1) (cons (TVar 2) nil))) Faux) Vrai)).
] *)
(** *** Notations usuelles pour les formules. *)

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

Local Notation "'X₁'":= (Var 1).
Local Notation "'X₂'":= (Var 2).
(* begin hide *)
Local Notation "'X₃'":= (Var 3).
Local Notation "'X₄'":= (Var 4).
Local Notation "'X₅'":= (Var 5).
Local Notation "'X₆'":= (Var 6).
Local Notation "'X₇'":= (Var 7).
Local Notation "'X₈'":= (Var 8).
Local Notation "'X₉'":= (Var 9).
Local Notation "'X₁₀'":= (Var 10).
(* end hide *)

Local Notation "'x₁'":= (TVar 1).
Local Notation "'x₂'":= (TVar 2).

(* begin hide *)
Local Notation "'x₃'":= (TVar 3).
Local Notation "'x₄'":= (TVar 4).
Local Notation "'x₅'":= (TVar 5).
Local Notation "'x₆'":= (TVar 6).
Local Notation "'x₇'":= (TVar 7).
Local Notation "'x₈'":= (TVar 8).
Local Notation "'x₉'":= (TVar 9).
Local Notation "'x₁₀'":= (TVar 10).
(* end hide *)

(* begin hide *)
Local Reserved Notation "'p₁' l" (at level 60).
Local Reserved Notation "'p₂' l" (at level 60).
Local Reserved Notation "'p₃' l" (at level 60).
Local Reserved Notation "'p₄' l" (at level 60).
Local Reserved Notation "'p₅' l" (at level 60).
Local Reserved Notation "'p₆' l" (at level 60).
Local Reserved Notation "'p₇' l" (at level 60).
Local Reserved Notation "'p₈' l" (at level 60).
(* end hide *)

Local Notation "'p₁' l":= (Pred 1 l).
Local Notation "'p₂' l":= (Pred 2 l).
(* begin hide *)
Local Notation "'p₃' l":= (Pred 3 l).
Local Notation "'p₄' l":= (Pred 4 l).
Local Notation "'p₅' l":= (Pred 5 l).
Local Notation "'p₆' l":= (Pred 6 l).
Local Notation "'p₇' l":= (Pred 7 l).
Local Notation "'p₈' l":= (Pred 8 l).
(* end hide *)

(* begin hide *)
Local Reserved Notation "'∀x₁' frm" (at level 60).
Local Reserved Notation "'∀x₂' frm" (at level 60).
Local Reserved Notation "'∀x₃' frm" (at level 60).
Local Reserved Notation "'∀x₄' frm" (at level 60).
Local Reserved Notation "'∀x₅' frm" (at level 60).
Local Reserved Notation "'∀x₆' frm" (at level 60).
Local Reserved Notation "'∀x₇' frm" (at level 60).
Local Reserved Notation "'∀x₈' frm" (at level 60).
Local Reserved Notation "'∀x₉' frm" (at level 60).
(* end hide *)

Local Notation "'∀x₁' frm":= (FORALL 1 frm).
Local Notation "'∀x₂' frm":= (FORALL 2 frm).

(* begin hide *)
Local Notation "'∀x₃' frm":= (FORALL 3 frm).
Local Notation "'∀x₄' frm":= (FORALL 4 frm).
Local Notation "'∀x₅' frm":= (FORALL 5 frm).
Local Notation "'∀x₆' frm":= (FORALL 6 frm).
Local Notation "'∀x₇' frm":= (FORALL 7 frm).
Local Notation "'∀x₈' frm":= (FORALL 8 frm).
Local Notation "'∀x₉' frm":= (FORALL 9 frm).
(* end hide *)

(* begin hide *)
Local Reserved Notation "'∃x₁' frm" (at level 60).
Local Reserved Notation "'∃x₂' frm" (at level 60).
Local Reserved Notation "'∃x₃' frm" (at level 60).
Local Reserved Notation "'∃x₄' frm" (at level 60).
Local Reserved Notation "'∃x₅' frm" (at level 60).
Local Reserved Notation "'∃x₆' frm" (at level 60).
Local Reserved Notation "'∃x₇' frm" (at level 60).
Local Reserved Notation "'∃x₈' frm" (at level 60).
Local Reserved Notation "'∃x₉' frm" (at level 60).
(* end hide *)

Local Notation "'∃x₁' frm":= (EXIST 1 frm).
Local Notation "'∃x₂' frm":= (EXIST 2 frm).
(* begin hide *)
Local Notation "'∃x₃' frm":= (EXIST 3 frm).
Local Notation "'∃x₄' frm":= (EXIST 4 frm).
Local Notation "'∃x₅' frm":= (EXIST 5 frm).
Local Notation "'∃x₆' frm":= (EXIST 6 frm).
Local Notation "'∃x₇' frm":= (EXIST 7 frm).
Local Notation "'∃x₈' frm":= (EXIST 8 frm).
Local Notation "'∃x₉' frm":= (EXIST 9 frm).
(* end hide *)


(* begin hide *)
Local Reserved Notation "'[' x ',' .. ',' y ']'"
    (at level 0, format "'[  ' [ '/' x ',' .. ',' y ] ']'").

Local Notation "'[' x ',' .. ',' y ']'" := (cons x .. (cons y nil) ..).
(* end hide *)

(** *** Exemples avec et sans notations: *)

(* **** formules: *)
(* begin hide *)
(** [
Check Vrai.
Check ⊤.
Check Faux.
Check ⊥.
Check (Ou Vrai Vrai).
Check (Ou ⊥ ⊤).
Check (Ou (Ou ⊤ ⊥) ⊤).
] *)
(* end hide *)
(** [
Check (Var 7).
Check X₇.
Check (Pred 1 (x₁::nil)).
Check (p₁ [x₁ , x₂ , x₃]).
Check (p₁ [x₁ , x₂ , x₃]).
Check (∀x₁ p₁ [x₁ , x₂ , x₃]).
Check (∀x₁∃x₂ p₁ [x₁ , x₂ , x₃]).
] *)

(** **** termes: *)

(** [
Check (TVar 7). 
Check x₇.
] *)

Scheme Equality for terme.
Open Scope bool_scope.


(** Décision de l'égalité sur les formules, Attention ce n'est pas la
    vraie égalité de formule puisque les noms de variables ne sont pas
    ignorés. *)
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
    | FORALL i φ, FORALL j ψ => Nat.eqb i j && formule_beq φ ψ
    | EXIST i φ, EXIST j ψ => Nat.eqb i j && formule_beq φ ψ
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


Ltac bool_to_prop :=
match goal with
  H:Nat.eqb _ _ = true |- _ => rewrite Nat.eqb_eq in H
| H:Nat.eqb _ _ = false |- _ => rewrite Nat.eqb_neq in H
| H: _ && _ = true |- _ => apply Bool.andb_true_iff in H;destruct H
end.

Ltac bP := repeat progress bool_to_prop.

Lemma formule_eq_okr : forall φ ψ:formule, formule_beq φ ψ = true -> φ = ψ.
Proof.
  intros φ ψ H.
  functional induction formule_beq φ ψ;auto;bP; try subst.  
  - auto.
  - rewrite IHb,IHb0;auto.
  - rewrite IHb,IHb0;auto.
  - rewrite IHb,IHb0;auto.
  - rewrite IHb;auto.
  - apply f_equal2;auto.
    apply Forall2_forallb2_iff in H0.
    rewrite terme_eq_true_eq_iff in H0.
    apply Forall2_eq_eq_iff.
    assumption.
  - rewrite IHb;auto.
  - rewrite IHb;auto.
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
  - rewrite (Nat.eqb_refl n).
    simpl.
    assumption.
  - rewrite (Nat.eqb_refl n).
    simpl.
    assumption.
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


(** * Définition de l'interprétation d'une formule *)

(** ** Valuation *)

(** Pour interpréter une formule on a besoin des éléments suivants:

    - une valuation [I] des variables propositionnelles,
    - un domaine d'interprétation pour les termes ([D]),
    - une valuation pour les termes, c'est-à-dire les variables
      de terme puisqu'on n'a pas de symbole de fonction.
      La valuation [interp_t] prend donc un numéro de variable
      de terme en argument et retourne un élément de [D].
    - une valuation pour les prédicats. Un prédicat est désigné
      par un entier, la valuation [interp_p] prend donc un entier
      et retourne l'interprétation du prédicat correspondant: une
      fonction de DxDxD... -> bool, où D est le domaine
      d'interprétation des terme.

      Par ailleurs on aura besoin de s'assurer que le domaine
      d'interprétation des termes est non vide, on se donne donc un
      témoin. *)

Record Valuation {D:Type} :=
  { vpredicat: nat -> (list D -> bool);
    vterme: terme -> D;
    vproposition: nat -> bool;
    temoin:D }.

(** ** Substitution dans la valuation des termes *)

(** Ajout (où modification) de la valeur d'une variable dans une
    interprétation. Utile pour l'interprétation des quantificateurs.
    On se place dans Z pour écrire la fonction. *)

Definition subst_in_interp interp i (n:Z) :=
  {| vpredicat:= interp.(vpredicat) ;
     vproposition:=interp.(vproposition);
     temoin:=interp.(temoin);

     (** On retourne n si Var i est demandée, sinon on passe la
            main à l'ancienne fonction. *)

     vterme:= fun trm:terme =>
                  let '(TVar j) := trm in
                  if Nat.eqb j i then n
                  else (interp.(vterme)) trm |}.

Local Notation "I [ i <- x ]" := (subst_in_interp I i x) (at level 10).

(** ** Interprétation d'une formule *)
(* begin hide *)
(* Local Reserved Notation "I '[' f ']->' b" (at level 51). *)
Local Reserved Notation "I '-[' f ']->' b" (at level 10).
(* end hide *)
(** La sémantique ne peut plus se définir comme une fonction car
    elle ne peut pas être le résultat d'un calcul (comment _calculer_
    la valeur de ∀x∈ℕ,P(x) si le domaine de x est infini).

    On définit donc l'interprétation comme une relation entre une
    formule, une interprétation et un booléen. On prouvera plus bas
    que cette relation est "fonctionnelle" en utilisant le
    tiers-exclu. Par ailleurs on prend Z comme domaine
    d'interprétation des termes mais cette définition est valable pour
    n'importe quel ensemble non vide. 

    On utilisera l'abus de notation suivant: [I-[f]->b] à la place de
    [(interp_def I f b)]. Attention toutefois à garder en mémoire qu'une
    interprétation I ne s'applique pas à une formule mais à une
    variable, c'est la fonction [interp_def] qui permet de généraliser
    une interprétation aux formules. *)
Inductive interp_def (I : Valuation) : formule -> bool -> Prop :=
  I_Vrai : I -[ ⊤ ]-> table_Vrai
| I_Faux : I -[⊥]-> table_Faux
| I_Var :  forall i b, vproposition I i = b -> I -[Var i]-> b
| I_Pred : forall i l b, vpredicat I i (map (vterme I) l) = b -> I -[Pred i l]-> b
| I_Non :  forall frm b₁ b, I -[frm]-> b₁ -> negb b₁ = b -> I -[¬ frm]-> b
| I_Ou :   forall f₁ f₂ b₁ b₂ b, I -[f₁]-> b₁ -> I -[f₂]-> b₂ -> b₁ || b₂ = b -> I -[f₁ ∨ f₂]-> b
| I_Et :   forall f₁ f₂ b₁ b₂ b, I -[f₁]-> b₁ -> I -[f₂]-> b₂ -> b₁ && b₂ = b -> I -[f₁ ∧ f₂]-> b
| I_Implique: forall f₁ f₂ b₁ b₂ b, I -[f₁]->b₁ -> I -[f₂]->b₂ -> implb b₁ b₂ = b -> I -[f₁ ⇒ f₂]->b
| I_Forall : forall f₁ n, (forall x : Z, (I [ n <- x ]) -[f₁]-> true) -> I -[FORALL n f₁]-> true
| I_NotForall : forall f₁ n, (exists x : Z, (I [n <- x]) -[f₁]-> false) -> I -[FORALL n f₁]-> false
| I_Exist : forall f₁ n, (exists x : Z, (I [n <- x]) -[f₁]-> true) -> I -[EXIST n f₁]-> true
| I_NotExist : forall f₁ n, (forall x : Z, (I [n <- x]) -[f₁]-> false) -> I -[EXIST n f₁]-> false
where "I '-[' f ']->' b" := (interp_def I f b). 


(* begin hide *)
Arguments interp_def : default implicits .


Ltac inversion_bool :=
  match goal with
    | H: context [orb false ?b₁] |- _  => rewrite Bool.orb_false_l in H;simpl in H
    | H: context [orb ?b₁ false] |- _  => rewrite Bool.orb_false_r in H; simpl in H
    | H: context [andb false ?b₁] |- _  => rewrite Bool.andb_false_l in H; simpl in H
    | H: context [andb ?b₁ false] |- _  => rewrite Bool.andb_false_r in H; simpl in H
    | H: context [and true ?b₁] |- _  => rewrite Bool.andb_true_l in H;simpl in H
    | H: context [andb ?b₁ true] |- _  => rewrite Bool.andb_true_r in H;simpl in H
    | H:(?b₁ && ?b₂)%bool = true |- _ =>
      let h := fresh "hb" in
      let h' := fresh "hb" in
      destruct (andb_prop _ _ H) as [h h']; clear H; simpl in h; simpl h'
    | H:(?b₁ || ?b₂)%bool = false |- _ =>
      let h := fresh "hb" in
      let h' := fresh "hb" in
      destruct (Bool.orb_false_elim _ _ H) as [h h']; clear H; simpl in h;simpl in h'
    | H: true = (?b₁ && ?b₂)%bool |- _ => symmetry in H
    | H:(negb ?b₁)%bool = true |- _ => rewrite Bool.negb_true_iff in H
    | H:(negb ?b₁)%bool = false |- _ => rewrite Bool.negb_false_iff in H
    | H: true = (negb ?b₁)%bool |- _ => symmetry in H
    | H: false = (negb ?b₁)%bool |- _ => symmetry in H
    | H: context [negb (?b1 || ?b2)] |- _ => rewrite Bool.negb_orb in H
    | H: context [(?b1 || negb (?b1))%bool] |- _ => rewrite Bool.orb_negb_r in H
    | H: context [(negb (?b1) || ?b1)%bool ] |- _ => rewrite Bool.orb_comm in H
    | H: context [negb (?b1 && ?b2)%bool] |- _ => rewrite Bool.negb_andb in H
    | H: context [(?b1 && negb (?b1))%bool] |- _ => rewrite Bool.andb_negb_r in H
    | H: context [(negb (?b1) && ?b1)%bool ] |- _ => rewrite Bool.andb_comm in H
    | H: context [negb (negb ?b1)] |- _ => rewrite Bool.negb_involutive in H
  end.

Ltac simpl_bool := repeat progress (inversion_bool; subst;simpl in *).

Ltac same_interp :=
  match goal with
    | H1 : interp_def ?I ?F ?b₁ , H2: interp_def ?I ?F ?b₁ |- _ => clear H2
    | H: interp_def ?I (?b₁ ∨ ?b₂) _ |- _ => inversion H; clear H; subst
    | H: interp_def ?I (?b₁ ∧ ?b₂) _ |- _ => inversion H; clear H; subst
    | H: interp_def ?I (?b₁ ⇒ ?b₂) _ |- _ => inversion H; clear H; subst
    | H: interp_def ?I (¬ ?b₁) _ |- _ => inversion H; clear H; subst
    | H: interp_def ?I ⊤ _ |- _ => inversion H; clear H; subst
    | H: interp_def ?I ⊥ _ |- _ => inversion H; clear H; subst
    | H: interp_def ?I (Var _) _ |- _ => inversion H; clear H; subst
    (*        | H: interp_def ?I (Var _) true |- _ => inversion H; clear H; subst
        | H: interp_def ?I (Var _) false |- _ => inversion H; clear H; subst
     *)
    | H: interp_def ?I (Pred _ _) _ |- _ => inversion H; clear H; subst
    | H: interp_def ?I (FORALL _ _) _ |- _ => inversion H; clear H; subst
    | H: interp_def ?I (EXIST _ _) _ |- _ => inversion H; clear H; subst
  end.

Ltac mysimpl tac := repeat progress first [
                             progress same_interp
                           | progress tac
                           | progress (subst;simpl in *)
                           | progress simpl_bool
                           ].

Ltac simp1 := mysimpl trivial.


(* On définit la notion de valuation équivalentes. v₁ et v₂ sont
    équivalentes si chacune des fonctions de v₁ et v₂ sont identique en
    tout point. Ceci est nécessaire pour la preuve de la méthode des
    tableaux (puisqu'on effectue des substitution dans les
    interprétations, mais cela n'a pas à apparaître dans le poly,
    c'est technique.*)


Inductive Interp_eq {D} (v₁ v₂:@Valuation D):Prop :=
  mk_valuation_eq:
    (eqExt2 (v₁.(vpredicat)) (v₂.(vpredicat)))
    -> (eqExt (v₁.(vterme)) (v₂.(vterme)))
    -> (eqExt (v₁.(vproposition)) (v₂.(vproposition)))
    -> Interp_eq v₁ v₂.

Lemma Interp_eq_refl D : Reflexive (@Interp_eq D).
Proof.
  red.
  intros x.
  constructor;auto.
  - apply eqExt2_refl.
  - apply eqExt_refl.
  - apply eqExt_refl.
Qed.


Lemma Interp_eq_sym D : Symmetric (@Interp_eq D).
Proof.
  red.
  intros x y h.
  constructor;auto.
  - apply eqExt2_sym.
    apply h.
  - apply eqExt_sym.
    apply h.
  - apply eqExt_sym.
    apply h.
Qed.

Lemma Interp_eq_trans D : Transitive (@Interp_eq D).
Proof.
  red.
  intros x y z h h'.
  constructor;auto.
  - eapply eqExt2_trans with (vpredicat y).
    apply h.
    apply h'.
  - eapply eqExt_trans with (vterme y).
    apply h.
    apply h'. 
  - eapply eqExt_trans with (vproposition y).
    apply h.
    apply h'. 
Qed.


Add Parametric Relation A B : (A -> B) eqExt
    reflexivity proved by (@eqExt_refl A B)
    symmetry proved by (@eqExt_sym A B)
    transitivity proved by (@eqExt_trans A B)
      as eqExt_rel.

Add Parametric Relation A B C : (A -> B -> C) eqExt2
    reflexivity proved by (@eqExt2_refl A B C)
    symmetry proved by (@eqExt2_sym A B C)
    transitivity proved by (@eqExt2_trans A B C)
      as eqExt2_rel.

Add Parametric Relation D : (@Valuation D) Interp_eq
    reflexivity proved by (@Interp_eq_refl D)
    symmetry proved by (@Interp_eq_sym D)
    transitivity proved by (@Interp_eq_trans D)
      as Interp_eq_rel.

Ltac inv h := inversion h; clear h; subst;simpl in *.

(** Des interprétation équivalentes donnent la même valeur à la même
    formule. *)

Add Parametric Morphism: interp_def
    with signature Interp_eq ==> Logic.eq ==> Logic.eq ==> iff as interp_morphism.
Proof.
  intros v₁ v₂ heq_interp f₁.
  inversion heq_interp as [heq_vpredicat heq_vterme heq_vproposition] ;clear heq_interp.
  revert v₁ v₂ heq_vpredicat heq_vterme heq_vproposition.
  induction f₁; intros v₁ v₂ heq_vpredicat heq_vterme heq_vproposition b₁;split; intro hv
  (* des versions instantiées de l'hypothèse de récurrence, attention
     pour les quantificateurs on a besoin d'autres instance (avec des
     substitutions). *)
  ; (try assert (IHf₁' := (IHf₁ _ _ heq_vpredicat heq_vterme heq_vproposition)))
  ; (try assert (IHf₁1' := (IHf₁1 _ _ heq_vpredicat heq_vterme heq_vproposition)))
  ; (try assert (IHf₁2' := (IHf₁2 _ _ heq_vpredicat heq_vterme heq_vproposition))).

  - inv hv. constructor.
  - inv hv. constructor.
  - inv hv. constructor.
  - inv hv. constructor.
  - inv hv. constructor. symmetry. apply heq_vproposition.
  - inv hv. constructor. apply heq_vproposition.
  - inv hv. econstructor;eauto. eapply IHf₁'. assumption.
  - inv hv. econstructor;eauto. apply IHf₁'. assumption.
  - inv hv.  econstructor;eauto.
    + eapply IHf₁1'. assumption.
    + eapply IHf₁2'. assumption.
  - inv hv.  econstructor;eauto.
    + eapply IHf₁1'. assumption.
    + eapply IHf₁2'. assumption.
  - inv hv.  econstructor;eauto.
    + eapply IHf₁1'. assumption.
    + eapply IHf₁2'. assumption.
  - inv hv.  econstructor;eauto.
    + eapply IHf₁1'. assumption.
    + eapply IHf₁2'. assumption.
  - inv hv.  econstructor;eauto.
    + eapply IHf₁1'. assumption.
    + eapply IHf₁2'. assumption.
  - inv hv.  econstructor;eauto.
    + eapply IHf₁1'. assumption.
    + eapply IHf₁2'. assumption.
  - inv hv.
    constructor.
    rewrite (map_ext (vterme v₂) (vterme v₁)).
    + symmetry. apply heq_vpredicat.
    + intros a.
      symmetry.
      rewrite heq_vterme.
      reflexivity.
  - inv hv.
    constructor.
    rewrite (map_ext (vterme v₂) (vterme v₁)).
    + apply heq_vpredicat.
    + intros a.
      symmetry.
      rewrite heq_vterme.
      reflexivity.
  - inv hv.
    + constructor.
      intros x.
      eapply IHf₁ with (v₁:= subst_in_interp v₁ n x) (v₂:= subst_in_interp v₂ n x).
      * unfold subst_in_interp;simpl.
        apply heq_vpredicat.
      * unfold subst_in_interp;simpl.
        intro y.
        rewrite heq_vterme.
        reflexivity.
      * unfold subst_in_interp;simpl.
        apply heq_vproposition.
      * auto.
    + constructor.
      destruct H2.
      exists x.
      eapply IHf₁ with (v₁:= subst_in_interp v₁ n x) (v₂:= subst_in_interp v₂ n x).
      * unfold subst_in_interp;simpl.
        apply heq_vpredicat.
      * unfold subst_in_interp;simpl.
        intro y.
        rewrite heq_vterme.
        reflexivity.
      * unfold subst_in_interp;simpl.
        apply heq_vproposition.
      * assumption.
  - inv hv.
    + constructor.
      intros x.
      eapply IHf₁ with (v₁:= subst_in_interp v₁ n x) (v₂:= subst_in_interp v₂ n x).
      * unfold subst_in_interp;simpl.
        apply heq_vpredicat.
      * unfold subst_in_interp;simpl.
        intro y.
        rewrite heq_vterme.
        reflexivity.
      * unfold subst_in_interp;simpl.
        apply heq_vproposition.
      * auto.
    + constructor.
      destruct H2.
      exists x.
      eapply IHf₁ with (v₁:= subst_in_interp v₁ n x) (v₂:= subst_in_interp v₂ n x).
      * unfold subst_in_interp;simpl.
        apply heq_vpredicat.
      * unfold subst_in_interp;simpl.
        intro y.
        rewrite heq_vterme.
        reflexivity.
      * unfold subst_in_interp;simpl.
        apply heq_vproposition.
      * assumption.
  - inv hv.
    + constructor.
      destruct H2.
      exists x.
      eapply IHf₁ with (v₁:= subst_in_interp v₁ n x) (v₂:= subst_in_interp v₂ n x).
      * unfold subst_in_interp;simpl.
        apply heq_vpredicat.
      * unfold subst_in_interp;simpl.
        intro y.
        rewrite heq_vterme.
        reflexivity.
      * unfold subst_in_interp;simpl.
        apply heq_vproposition.
      * assumption.
    + constructor.
      intros x.
      eapply IHf₁ with (v₁:= subst_in_interp v₁ n x) (v₂:= subst_in_interp v₂ n x).
      * unfold subst_in_interp;simpl.
        apply heq_vpredicat.
      * unfold subst_in_interp;simpl.
        intro y.
        rewrite heq_vterme.
        reflexivity.
      * unfold subst_in_interp;simpl.
        apply heq_vproposition.
      * auto.
  - inv hv.
    + constructor.
      destruct H2.
      exists x.
      eapply IHf₁ with (v₁:= subst_in_interp v₁ n x) (v₂:= subst_in_interp v₂ n x).
      * unfold subst_in_interp;simpl.
        apply heq_vpredicat.
      * unfold subst_in_interp;simpl.
        intro y.
        rewrite heq_vterme.
        reflexivity.
      * unfold subst_in_interp;simpl.
        apply heq_vproposition.
      * assumption.
    + constructor.
      intros x.
      eapply IHf₁ with (v₁:= subst_in_interp v₁ n x) (v₂:= subst_in_interp v₂ n x).
      * unfold subst_in_interp;simpl.
        apply heq_vpredicat.
      * unfold subst_in_interp;simpl.
        intro y.
        rewrite heq_vterme.
        reflexivity.
      * unfold subst_in_interp;simpl.
        apply heq_vproposition.
      * auto.
Qed.
(* end hide *)

(** ** Déterminisme et totalité de l'interprétation d'une formule.

  Pour les logique précédente ces deux propriétés étaient des
  conséquences du fait que l'interprétation était définie par une
  _fonction_. Maintenant que l'interprétation est une relation il faut
  démontrer que cette relation correspond en fa it à une fonction (non
  calculable). *)

Lemma interp_def_det :
  forall f₁ interp b₁,
    interp_def interp f₁ b₁
    -> forall b₂, interp_def interp f₁ b₂ -> b₁ = b₂.
Proof.
  intros f₁.
  induction f₁;intros interp b₁ h b₂ h';try solve [simp1].
  - simp1. rewrite (IHf₁ _ _ H0 _ H1). reflexivity.
  - simp1. rewrite (IHf₁1 _ _ H1 _ H3). rewrite (IHf₁2 _ _ H2 _ H4). reflexivity.
  - simp1. rewrite (IHf₁1 _ _ H1 _ H3). rewrite (IHf₁2 _ _ H2 _ H4). reflexivity.
  - simp1. rewrite (IHf₁1 _ _ H1 _ H3). rewrite (IHf₁2 _ _ H2 _ H4). reflexivity.
  - simp1.
    + destruct H3. specialize (H2 x).
      rewrite (IHf₁ _ _ H2 _ H). reflexivity.
    + destruct H2. specialize (H3 x).
      rewrite (IHf₁ _ _ H3 _ H). reflexivity.
  - simp1.
    + destruct H2. specialize (H3 x).
      rewrite (IHf₁ _ _ H3 _ H). reflexivity.
    + destruct H3. specialize (H2 x).
      rewrite (IHf₁ _ _ H2 _ H). reflexivity.
Qed.


Ltac finish := solve[left;econstructor;eauto 3
                    |right;econstructor;eauto 3].



(* begin show *)
(** Ceci introduit l'axiome suivant: [forall P : Prop, P \/ ~ P]. *)

From Stdlib Require Import Classical. 
(* end show *)


(** La relation d'interprétation est totale: pour toute formule et
    toute interprétation il existe une valeur interprétation
    booléenne. Pour information cette preuve utilise le tiers-exclu. *)

Lemma interp_def_tot :
  forall f₁ interp,
    interp_def interp f₁ true \/ interp_def interp f₁ false.
Proof.
  intros f₁.
  induction f₁;intros interp. (*;try solve [simp''].*)
  - left. constructor 1.
  - right. constructor 2.
  - destruct (vproposition interp n) eqn:heq; finish.
  - destruct (IHf₁ interp);finish.
  - destruct (IHf₁1 interp);destruct (IHf₁2 interp); finish.
  - destruct (IHf₁1 interp);destruct (IHf₁2 interp); finish.
  - destruct (IHf₁1 interp);destruct (IHf₁2 interp); finish.
  - destruct (interp.(vpredicat) n (map interp.(vterme) l)) eqn:heq.
    + left. constructor. assumption.
    + right. constructor. assumption.
  - destruct (classic (forall x : Z, interp_def (subst_in_interp interp n x) f₁ true)).
    + left. constructor. assumption.
    + right. apply I_NotForall.
      apply not_all_ex_not in H.
      destruct H.
      destruct (IHf₁ (subst_in_interp interp n x)).
      * contradiction.
      * { exists x. assumption. }
  - destruct (classic (exists x : Z, interp_def (subst_in_interp interp n x) f₁ true)).
    + left. constructor. assumption.
    + right. apply I_NotExist.
      intros x.
      apply not_ex_all_not with (n:=x) in H.
      destruct (IHf₁ (subst_in_interp interp n x)).
      * contradiction.
      * assumption.
Qed.

(** Corollaire du déterminisme + totalité de l'interpétation. *)

Lemma interp_not_true :
  forall f₁ interp,
    ~ interp_def interp f₁ true <-> interp_def interp f₁ false.
Proof.
  intros f₁ interp.
  split;intro h.
  - destruct (interp_def_tot f₁ interp).
    + contradiction.
    + assumption.
  - intro abs.
    assert (true=false).
    + apply (interp_def_det f₁ interp).
      * assumption.
      * assumption.
    + discriminate.
Qed.

(* begin hide *)
(* D'autres versions plus pratique suivant le contexte. *)

Lemma interp_not_false :
  forall f₁ interp,
    ~ interp_def interp f₁ false <-> interp_def interp f₁ true.
Proof.
  intros f₁ interp.
  split; intro h.
  - destruct (interp_def_tot f₁ interp).
    + assumption.
    + contradiction.
  - intro abs.
    assert (true=false).
    + apply (interp_def_det f₁ interp).
      * assumption.
      * assumption.
    + discriminate.
Qed.

Lemma interp_true_false :
  forall f₁ interp,
    interp_def interp f₁ false
    -> interp_def interp f₁ true
    -> False.
Proof.
  intros f₁ interp H H0.
  rewrite <- interp_not_false in H0.
  contradiction.
Qed.

(* end hide *)
(* begin hide *)

Ltac simp :=
  mysimpl
    ltac:(first [solve[trivial] |
                 match goal with
                   | H : ¬interp_def ?v ?F true |- _ => rewrite interp_not_true in H
                   | H : ¬interp_def ?v ?F false |- _  => rewrite interp_not_false in H
                   | H : interp_def ?v ?F true , H2: interp_def ?v ?F false |- _ => 
                     exfalso; apply (interp_true_false F v);assumption
                   | H : interp_def ?v ?F ?b₁ , H2: interp_def ?v ?F ?b₂ |- _ => 
                     assert (b₁=b₂);
                       [ apply interp_def_det with (f₁:=F) (interp:=v);assumption
                       | try subst]
                 end]).

(* end hide *)

(** ** Exemples d'interprétations *)

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

  Definition III:Valuation := {| vpredicat:=vp; vterme:=vt; vproposition:=v₁; temoin:=0%Z |}.
  Definition III':Valuation := {| vpredicat:=vp; vterme:=vt; vproposition:=v₂; temoin:=0%Z |}.

  #[local] Hint Constructors interp_def: interp.

  Lemma Ex1: interp_def III (⊤ ⇒ (⊤ ∨ ⊥)) true.
  Proof.
    eauto with interp.
  Qed.

  Lemma Ex1': interp_def III (⊤ ⇒ (⊤ ∨ ⊥)) false.
  Proof.
    eauto with interp.
  Abort.

  Lemma Ex2: interp_def III' (⊤ ⇒ (⊤ ∨ ⊥)) true.
  Proof.
    eauto with interp.
  Qed.

  Lemma Ex3: interp_def III' (p₁[x₁]) true.
  Proof.
    eauto with interp.
  Qed.

  Lemma Ex4: interp_def III' (p₁[x₁] ⇒ ⊥) false.
  Proof.
    eauto with interp.
  Qed.

  Lemma Ex5: interp_def III' (p₁[x₁] ⇒ (⊥ ∧ ⊥)) false.
  Proof.
    eauto with interp.
  Qed.

  Lemma Ex5': interp_def III' (p₁[x₁] ⇒ (⊥ ∧ ⊥)) true.
  Proof.
    eauto with interp.
  Abort.

End Exemples.

(** * Conséquence, modèle etc *)

(** On applique les définitions de conséquence, modèle etc du
    chapitre #<a href="logique_generique.html">logique_generique</a>#
    avec les notions de valuation et d'interprétation ci-dessous. *)

(** l'interprétation n'est pas nécessairement décidable. En effet
    l'ensemble sur lequel sont quantifiées les variables peut être
    infini. *)

(* begin hide *)
Module LogPredVar <: Logique.
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
  Definition interpretation: valuation -> formule -> bool -> Prop := interp_def.

  (* begin hide *)
  Lemma interpretation_unique:
    forall v f b1 b2, interpretation v f b1 -> interpretation v f b2 -> b1= b2.
  Proof.
    intros v f b1 b2 H H0.
    eapply interp_def_det;eauto.
  Qed.
  (* end hide *)
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
Local Tactic Notation "smpl*" := repeat progress smpl.
(* end hide *)

Module Exemples_modeles.
  #[local] Hint Constructors interp_def: interp.

  Lemma modele1 : forall v n, ⊧[v] Var n ∨ ¬ (Var n).
  Proof.
    intros v n.
    destruct (vproposition v n) eqn:heq.
    - econstructor;eauto with interp.
    - econstructor;eauto with interp.
  Qed.

  Lemma modele2 : forall v, ⊧[v] (X₁ ∨ ¬ X₂) ∨ X₂.
  Proof.
    intros v.
    destruct (v.(@vproposition Z) 1) eqn:heq.
    - destruct (v.(@vproposition Z) 2) eqn:heq'.
      + econstructor;eauto with interp.
      + econstructor;eauto with interp.
    - destruct (v.(@vproposition Z) 2) eqn:heq'.
      + econstructor;eauto with interp.
      + econstructor;eauto with interp.
  Qed.

End Exemples_modeles.


Module Exemples_conseq.

  Lemma conseq1: (X₁∨¬X₂) ∧ X₂ ⊧ X₁.
  Proof.
    unfold consequence,est_modele.
    intros v h;simp.
    case_eq (vproposition v 1);intros.
    - constructor. assumption.
    - rewrite hb0 in *.
      rewrite H in *.
      simpl in *.
      discriminate.
  Qed.

End Exemples_conseq.

(** * Preuves d'équivalences entre formules *)

Lemma eq_implique : forall x y : formule, x ⇒ y ≡ ¬x ∨ y.
Proof.
  intros x y.
  simpl.
  unfold equiv,consequence,est_modele. simpl.
  split;intros.
  - simp.
    destruct b₁;simp.
    + apply I_Ou with false true;auto.
      apply I_Non with true;auto.
    + apply I_Ou with true b₂;auto.
      apply I_Non with false;auto.
  - simp.
    destruct b₁0;simp.
    + apply I_Implique with true true;auto.
    + apply I_Implique with false b₂;auto;simp.
Qed.

Lemma eq_et : forall x y: formule, (x ∧ y) ≡ ¬ (¬x ∨ ¬y).
Proof.
  intros x y.
  unfold equiv,consequence,est_modele. simpl.
  split;intros.
  - simp. apply I_Non with false;auto.
    apply I_Ou with false false;auto.
    + apply I_Non with true;auto.
    + apply I_Non with true;auto.
  - simp.
    apply I_Et with true true;auto.
Qed.

Lemma eq_not : ⊥ ≡ ¬ ⊤.
                 Proof.
                   simpl.
                   unfold equiv,consequence,est_modele. simpl.
                   split;intros.
                   - simp.
                   - simp. discriminate.
                 Qed.

Lemma eq_not_exist : forall i, forall f : formule, (¬ (FORALL i f)) ≡ EXIST i (¬f).
Proof.
  intros i f.
  unfold equiv,consequence,est_modele.
  split;intros;simp.
  - discriminate.
  - destruct H4.
    apply I_Exist.
    exists (x).
    apply I_Non with false.
    + assumption.
    + reflexivity.
  - destruct H1.
    apply I_Non with false. simp.
    + eapply I_NotForall.
      exists (x).
      assumption.
    + reflexivity.
Qed.


Lemma eq_not_forall : forall i, forall f : formule, (¬ (EXIST i f)) ≡ FORALL i (¬f).
Proof.
  intros i f.
  unfold equiv,consequence,est_modele.
  split;intros;simp.
  - discriminate.
  - apply I_Forall.
    intros x.
    apply I_Non with false.
    + auto.
    + reflexivity.
  - apply I_Non with false.
    + apply I_NotExist.
      intros x.
      specialize (H1 x).
      simp.
    + reflexivity.
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

Lemma impl_not: forall A B : Prop, (A -> B) -> ~B -> ~A.
Proof.
  intros A B H H0.
  intro ha.
  apply H in ha.
  contradiction.
Qed.

(* Generaliser avec l'autre morphism (extensionalité)? *)
Add Parametric Morphism: interp_def
    with signature Logic.eq ==> equiv ==> Logic.eq ==> iff as interp_morphism2.
Proof.
  intros v x y.
  unfold equiv, consequence, est_modele.
  destruct 1.
  specialize (H v).
  specialize (H0 v).
  split;intros.
  - destruct y1.
    + auto.
    + assert (~ interp_def v y true).
      * apply interp_not_true in H1.
        apply impl_not with (B:=interp_def v x true).
        { assumption. }
        { assumption. }
      * apply interp_not_true. assumption.
  - destruct y1.
    + auto.
    + assert (~ interp_def v x true).
      * apply interp_not_true in H1.
        apply impl_not with (B:=interp_def v y true).
        { assumption. }
        { assumption. }
      * apply interp_not_true. assumption.
Qed.

Add Parametric Morphism: Et
    with signature equiv ==> equiv ==> equiv as and_morphism.
Proof.
  intros x y [h1 h2] x0 y0 [h3 h4].
  split.
  - red. intros v H1.
    unfold equiv, consequence, est_modele in *.
    destruct (interp_def_tot x v);destruct (interp_def_tot x0 v);auto.
    + econstructor;eauto.
    + simp. discriminate.
    + simp. discriminate.
    + simp. discriminate.
  - red. intros v H1.
    unfold equiv, consequence, est_modele in *.
    destruct (interp_def_tot y v);destruct (interp_def_tot y0 v);auto.
    + econstructor;eauto.
    + simp. discriminate.
    + simp. discriminate.
    + simp. discriminate.
Qed.

Add Parametric Morphism: Ou
    with signature equiv ==> equiv ==> equiv as Ou_morphism.
Proof.
  intros x y [h1 h2] x0 y0 [h3 h4].
  split.
  - red. intros v H1.
    unfold equiv, consequence, est_modele in *.
    destruct (interp_def_tot x v);destruct (interp_def_tot x0 v);auto.
    + econstructor;eauto.
    + simp.
      specialize (h1 v).
      specialize (h2 v).
      specialize (h3 v).
      specialize (h4 v).
      apply I_Ou with true false;auto.
      apply interp_not_true in H0.
      apply impl_not with (A:=interp_def v y0 true) in H0.
      * apply interp_not_true.
        assumption.
      * assumption.
    + simp.
      specialize (h1 v).
      specialize (h2 v).
      specialize (h3 v).
      specialize (h4 v).
      apply I_Ou with false true;auto.
      apply interp_not_true in H.
      apply impl_not with (A:=interp_def v y true) in H.
      * apply interp_not_true.
        assumption.
      * assumption.
    + simp. discriminate.
  - red. intros v H1.
    unfold equiv, consequence, est_modele in *.
    destruct (interp_def_tot x v);destruct (interp_def_tot x0 v);auto.
    + simp. econstructor;eauto.
    + simp. econstructor;eauto.
    + simp. econstructor;eauto.
    + simp.
      destruct b₁.
      * apply h2 in H4. simp.
      * { destruct b₂.
          - apply  h4 in H5. simp.
          - discriminate H7. }
Qed.            


Add Parametric Morphism: Non
    with signature equiv ==> equiv as Non_morphism.
Proof.
  intros x y H.
  split.
  - unfold equiv, consequence, est_modele in *.
    destruct H as [H' H''].
    intros v H.
    simp.
    apply interp_not_true in H1.
    eapply I_Non with false.
    + apply interp_not_true.
      apply (impl_not _ _ (H'' v)).
      assumption.
    + reflexivity.
  - unfold equiv, consequence, est_modele in *.
    destruct H as [H' H''].
    intros v H.
    simp.
    apply interp_not_true in H1.
    eapply I_Non with false.
    + apply interp_not_true.
      apply (impl_not _ _ (H' v)).
      assumption.
    + reflexivity.
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
  unfold consequence, est_modele.
  intros H v H0.
  simpl in H0.
  exfalso.
  destruct (interp_def_tot f₁ v);simp.
  - eapply interp_true_false;eauto.
  - discriminate.
Qed.

(** Pour prouver f ⊧ g on peut prouver f ∧ ¬g ⊧ ⊥ .  *)

Lemma conseq_by_contradiction: forall f₁ f₂: formule,  ¬f₂ ∧ f₁ ⊧ ⊥ -> f₁ ⊧ f₂.
Proof.
  intros f₁ f₂.
  unfold consequence, est_modele.
  simpl.
  intros H v heq.
  specialize (H v).
  destruct (interp_def_tot f₂ v).
  - assumption.
  - absurd (interp_def v ⊥ true).
    + intro abs. simp.
    + apply H.
      apply I_Et with true true.
      * econstructor;eauto.
      * assumption.
      * reflexivity.
Qed.

(** * Preuve par la méthode des tableaux  *)

(** ** Lemmes auxilaires pour la méthode des tableaux *)

Lemma and_affaiblissement_conseq : forall v f₁ f₂, v-[f₁∧f₂]->true -> v-[f₁]->true.
Proof.
  intros v f₁ f₂ H.
  simp.
Qed.

Lemma and_affaiblissement_contr : forall f₁ f₂, f₁ ⊧ ⊥ -> f₁∧f₂ ⊧ ⊥ .
Proof.
  intros f₁ f₂ H.
  unfold consequence, est_modele.
  intros v H0.
  simp.
  apply H.
  assumption.
Qed.

Lemma Et_sym : forall f₁ f₂, f₁ ∧ f₂ ≡ f₂ ∧ f₁.
Proof.
  intros f₁ f₂.
  split.
  - intros v H.
    inversion H. subst. clear H.
    simp.
    econstructor;eauto.
  - intros v H.
    inversion H. subst. clear H.
    simp.
    econstructor;eauto.
Qed.


Lemma Et_assoc : forall f₁ f₂ f₃, f₁ ∧ (f₂ ∧ f₃) ≡ (f₁ ∧ f₂) ∧ f₃.
Proof.
  intros f₁ f₂ f₃.
  split.
  - repeat red; simpl.
    intros v H.
    inversion H. subst. clear H.
    simp. repeat (econstructor;eauto).
  - repeat red; simpl.
    intros v H.
    inversion H. subst. clear H.
    simp. repeat (econstructor;eauto).
Qed.


Function extraction_disjuntion (f F: formule): option formule :=
  match F with
    | (g ∧ F') =>
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
Eval compute in (extraction_disjuntion  ((X₁ ∨ ¬X₂) ∧ X₂) (((X₁ ∨ ¬X₂) ∧ X₂) ∧ ¬X₁)). ] *)
(* Eval compute in (extraction_disjuntion  ). *)

Lemma Et_et_true : forall f, f ≡ f ∧ ⊤.
Proof.
  intros f.
  rewrite Et_sym.
  unfold equiv,consequence,est_modele.
  split;intros.
  - apply I_Et with true true.
    + constructor.
    + assumption.
    + reflexivity.
  - inv H.
    inv H2.
    subst;simpl in *.
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
                     ((f₁ ∧ F ⊧ ⊥)
                      /\ (f₂ ∧ F ⊧ ⊥))
                     -> (f₁ ∨ f₂) ∧ F ⊧ ⊥.
Proof.
  intros F f₁ f₂ H.
  destruct H as [h h'].
  unfold consequence,est_modele,equiv in *.
  intros v H0.
  specialize (h v).
  specialize (h' v).
  inversion H0. subst. clear H0. simp.
  apply Bool.orb_true_iff in hb. destruct hb as [hb | hb];subst.
  - apply h. repeat (econstructor;eauto).
  - apply h'. repeat (econstructor;eauto).
Qed.



Lemma tableau_Ou' : forall f₁ f₂,
                     (f₁ ⊧ Faux)
                     /\ (f₂ ⊧ Faux)
                     -> (f₁ ∨ f₂) ⊧ Faux.
Proof.
  intros f₁ f₂ H.
  destruct H as [h h'].
  unfold consequence,est_modele,equiv in *.
  intros v H0.
  specialize (h v).
  specialize (h' v).
  inversion H0. subst. clear H0.
  apply Bool.orb_true_iff in H5. destruct H5 as [hb | hb];subst.
  - apply h. assumption.
  - apply h'. assumption.
Qed.


Lemma tableau_nonEt : forall F f₁ f₂,
                        (¬f₁ ∧ F ⊧ ⊥) /\ (¬f₂ ∧ F ⊧ ⊥)
                        -> ¬(f₁ ∧ f₂) ∧ F ⊧ ⊥.
Proof.
  intros F f₁ f₂ H.
  destruct H as [h h'].
  unfold consequence,est_modele,equiv in *.
  intros v H0.
  specialize (h v).
  specialize (h' v).
  simp.
  apply Bool.andb_false_iff in hb. destruct hb as [hb | hb];subst.
  - apply h. repeat (econstructor;eauto).
  - apply h'. repeat (econstructor;eauto).
Qed.

Lemma tableau_nonEt' : forall f₁ f₂,
                        (¬f₁ ⊧ ⊥) /\ (¬f₂ ⊧ ⊥)
                        -> ¬(f₁ ∧ f₂) ⊧ ⊥.
Proof.
  intros f₁ f₂ H.
  destruct H as [h h'].
  unfold consequence,est_modele,equiv in *.
  intros v H0.
  specialize (h v).
  specialize (h' v).
  simp.
  apply Bool.andb_false_iff in H2. destruct H2 as [hb | hb];subst.
  - apply h. repeat (econstructor;eauto).
  - apply h'. repeat (econstructor;eauto).
Qed.

Lemma tableau_implique : forall F f₁ f₂,
                           (¬f₁ ∧ F ⊧ ⊥) /\ (f₂ ∧ F ⊧ ⊥)
                           -> (f₁ ⇒ f₂) ∧ F ⊧ ⊥.
Proof.
  intros F f₁ f₂ H.
  destruct H as [h h'].
  unfold consequence,est_modele,equiv in *.
  intros v H0.
  specialize (h v).
  specialize (h' v).
  simp.
  apply Bool.le_implb in hb.
  destruct b₁0.
  - apply h'. repeat (econstructor;eauto). simp.
  - apply h.  repeat (econstructor;eauto).
Qed.

Lemma tableau_implique' : forall f₁ f₂,
                           (¬f₁ ⊧ ⊥) /\ (f₂ ⊧ ⊥)
                           -> (f₁ ⇒ f₂) ⊧ ⊥.
Proof.
  intros f₁ f₂ H.
  destruct H as [h h'].
  unfold consequence,est_modele,equiv in *.
  intros v H0.
  specialize (h v).
  specialize (h' v).
  simp.
  apply Bool.le_implb in H5.
  destruct b₁.
  - apply h'. repeat (econstructor;eauto). simp.
  - apply h.  repeat (econstructor;eauto).
Qed.


Lemma tableau_Et : forall F f₁ f₂, f₁ ∧ f₂ ∧ F ⊧ ⊥ -> (f₁ ∧ f₂) ∧ F ⊧ ⊥.
Proof.
  intros F f₁ f₂ h.
  unfold consequence,est_modele,equiv in *.
  simpl in *.
  intros v H0.
  specialize (h v).
  simp.
  apply h. repeat (econstructor;eauto).
Qed.


Lemma tableau_Et' : forall f₁ f₂, f₁ ∧ f₂ ⊧ ⊥ -> (f₁ ∧ f₂) ⊧ ⊥.
Proof.
  intros f₁ f₂ h.
  unfold consequence,est_modele,equiv in *.
  simpl in *.
  intros v H0.
  specialize (h v).
  simp.
  apply h. repeat (econstructor;eauto).
Qed.


Lemma tableau_nonimplique : forall F f₁ f₂, f₁ ∧ ¬f₂ ∧ F ⊧ ⊥ -> ¬(f₁ ⇒ f₂) ∧ F ⊧ ⊥.
Proof.
  intros F f₁ f₂ h.
  unfold consequence,est_modele,equiv in *.
  simpl in *.
  intros v H0.
  specialize (h v).
  simp.
  destruct b₁.
  - apply h. repeat (econstructor;eauto). simp.
  - apply h.  repeat (econstructor;eauto).
Qed.


Lemma tableau_nonimplique' : forall f₁ f₂, f₁ ∧ ¬f₂ ⊧ ⊥ -> ¬(f₁ ⇒ f₂) ⊧ ⊥.
Proof.
  intros f₁ f₂ h.
  unfold consequence,est_modele,equiv in *.
  simpl in *.
  intros v H0.
  specialize (h v).
  simp.
  destruct b₁0.
  - apply h. repeat (econstructor;eauto). simp.
  - apply h.  repeat (econstructor;eauto).
Qed.


Lemma tableau_nonOu : forall F f₁ f₂, ¬f₁ ∧ ¬f₂ ∧ F ⊧ ⊥ -> ¬(f₁ ∨ f₂) ∧ F ⊧ ⊥.
Proof.
  intros F f₁ f₂ h.
  unfold consequence,est_modele,equiv in *.
  intros v H0.
  specialize (h v).
  simp.
  apply h.
  repeat (econstructor;eauto).
Qed.

Lemma tableau_nonOu' : forall f₁ f₂, ¬f₁ ∧ ¬f₂ ⊧ ⊥ -> ¬(f₁ ∨ f₂) ⊧ ⊥.
Proof.
  intros f₁ f₂ h.
  unfold consequence,est_modele,equiv in *.
  intros v H0.
  specialize (h v).
  simp.
  apply h.
  repeat (econstructor;eauto).
Qed.

Lemma tableau_ferme_branche : forall F f, (F ∧ f) ∧ ¬f ⊧ ⊥.
Proof.
  unfold consequence,est_modele,equiv in *.
  intros F f v H.
  simp.
  discriminate.
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
  simp.
  discriminate.
Qed.


Lemma p_et_p_eq : forall a, a∧a ≡ a.
Proof.
  intros a.
  unfold equiv,consequence,est_modele.
  simpl.
  split;intros;simp.
  repeat (econstructor;eauto).
Qed.

(** ** Les règles pour les quantificateurs *)


(** Ces règles sont plus compliquées à exprimer et à démontrer car
    elle font appelle à la notion de variables liées, libre et
    fraîches. On commence par définir ces notions et leur propriétés,
    puis on énonce les règles pour les quantificateurs. *)

(** *** Notions de variables (de terme) fraîches, liées etc. *)

Inductive is_fresh_terme_list (i:nat): list terme -> Prop :=
| isFreshTrmNil : is_fresh_terme_list i nil
| isFreshTrmCons : forall j l, is_fresh_terme_list i l -> i<>j
                               -> is_fresh_terme_list i (TVar j::l).

(** Une variable de terme [i] est fraîche dans la formule φ si elle
    n'apparaît nulle part dans φ. *)
Inductive is_fresh i: formule -> Prop :=
| isFreetrue: is_fresh i ⊤
| isFreefalse: is_fresh i ⊥
| isFreeV: forall j, is_fresh i (Var j)
| isFreeNon: forall φ, is_fresh i φ -> is_fresh i (¬φ) 
| isFreeEt: forall φ ψ, is_fresh i φ ->is_fresh i ψ -> is_fresh i (φ∧ψ)
| isFreeOr: forall φ ψ, is_fresh i φ -> is_fresh i ψ -> is_fresh i (φ∨ψ)
| isFreeImplique: forall φ ψ, is_fresh i φ -> is_fresh i ψ -> is_fresh i (φ ⇒ ψ)
| isFreePred: forall p lt, is_fresh_terme_list i lt -> is_fresh i (Pred p lt)
| isFreeFORALL: forall j φ, is_fresh i φ  ->  i<>j -> is_fresh i (FORALL j φ) 
| isFreeEXIST: forall j φ, is_fresh i φ ->  i<>j -> is_fresh i (EXIST j φ).

(** Une variable [i] est non-liée dans une formule φ si elle n'a pas
    d'occurrence dans un quantificateur. *)
Inductive is_not_bound i: formule -> Prop := 
| isNotBoundtrue: is_not_bound i ⊤
| isNotBoundfalse: is_not_bound i ⊥
| isNotBoundV: forall j, is_not_bound i (Var j)
| isNotBoundNon: forall φ, is_not_bound i φ -> is_not_bound i (¬φ)
| isNotBoundEt: forall φ ψ, is_not_bound i φ ->is_not_bound i ψ -> is_not_bound i (φ∧ψ)
| isNotBoundOr: forall φ ψ, is_not_bound i φ -> is_not_bound i ψ -> is_not_bound i (φ∨ψ)
| isNotBoundImplique: forall φ ψ, is_not_bound i φ
                                  -> is_not_bound i ψ -> is_not_bound i (φ ⇒ ψ)
| isNotBoundPred: forall p lt, is_not_bound i (Pred p lt)
| isNotBoundFORALL: forall j φ, is_not_bound i φ  ->  i<>j -> is_not_bound i (FORALL j φ)
| isNotBoundEXIST: forall j φ, is_not_bound i φ ->  i<>j -> is_not_bound i (EXIST j φ).

(** Une variable fraîche est également non-liée *)

Lemma fresh_is_not_bound : forall φ i, is_fresh i φ -> is_not_bound i φ.
Proof.
  intros φ i H.
  induction H;try constructor;auto.
Qed.

(* begin hide *)

Lemma subst_fresh_id_map:
  forall i lt,
    is_fresh_terme_list i lt
    -> forall v x, (map (vterme v) lt) = (map (vterme (subst_in_interp v i x)) lt).
Proof.
  intros i lt h.
  induction h;simpl;intros.
  - reflexivity.
  - rewrite (beq_nat_diff_rev _ _ H).
    unfold subst_in_interp in IHh;simpl in IHh.
    rewrite <- IHh.
    reflexivity.
Qed.



Lemma subst_fresh_id_pred : 
  forall (i : ℕ) (p : ℕ) (lt : list terme),
    is_fresh_terme_list i lt
    -> forall  (v : Valuation) (x : Z),
         ((⊧[subst_in_interp v i x] (Pred p lt)) <-> (⊧[v] (Pred p lt))).
Proof.
  intros i p lt H v x.
  split.
  - intros H0.
    inversion H0;clear H0.
    rewrite <- subst_fresh_id_map in H4.
    + subst.
      simpl in H4.
      constructor.
      assumption.
    + assumption.
  - intros H0.
    inversion H0;clear H0.
    rewrite (subst_fresh_id_map i _ H _ x) in H4.
    + subst.
      constructor.
      unfold subst_in_interp at 1.
      unfold vpredicat.
      assumption.
Qed.

Lemma subst_permut:
  forall v i j x y φ,
    i<>j
    -> forall b, (subst_in_interp (subst_in_interp v j y) i x) -[φ]-> b <-> (subst_in_interp (subst_in_interp v i x) j y) -[φ]-> b.
Proof.
  intros v i j x y φ H b.
  assert (Interp_eq (subst_in_interp (subst_in_interp v j y) i x) (subst_in_interp (subst_in_interp v i x) j y)).
  { 
    constructor; unfold subst_in_interp;simpl.
    - reflexivity.
    - intro.
      destruct x0.
      + destruct (eq_nat_dec i n);subst.
        rewrite Nat.eqb_refl.
        * apply Nat.eqb_neq in H.
          rewrite H.
          reflexivity.
        * { destruct (eq_nat_dec j n);subst.
            + rewrite Nat.eqb_refl.
              rewrite (beq_nat_diff_rev _ _ H).
              reflexivity.
            + rewrite (beq_nat_diff_rev _ _ n0).
              rewrite (beq_nat_diff_rev _ _ n1).
              reflexivity. }
    - reflexivity. }
  rewrite H0.
  reflexivity.
Qed.

Lemma subst_fresh_id_true: forall i φ, is_fresh i φ -> forall v x, ⊧[subst_in_interp v i x] φ  <-> ⊧[v] φ.
Proof.
  intros i φ H.
  induction H; intros v x;split;intro h;unfold est_modele in *.
  - constructor.
  - constructor.
  - inversion h;subst;simpl in *. 
  - inversion h.
  - inversion h;subst;simpl in *. 
    constructor.
    assumption.
  - inversion h.
    constructor.
    simpl.
    assumption.
  - inversion h;subst;simpl in *.
    apply Bool.negb_true_iff in H2;subst.
    apply I_Non with false;auto.
    apply interp_not_true.
    rewrite <- IHis_fresh.
    apply interp_not_true.
    eassumption.
  - inversion h;subst.
    apply Bool.negb_true_iff in H2;subst.
    apply I_Non with false;auto.
    apply interp_not_true.
    rewrite IHis_fresh.
    apply interp_not_true.
    assumption.
  - inversion h;subst;clear h.
    apply Bool.andb_true_iff in H6.
    destruct H6.
    subst.
    apply IHis_fresh1 in H3.
    apply IHis_fresh2 in H4.
    econstructor;eauto.
  - inversion h;subst;simpl in *. 
    apply Bool.andb_true_iff in H6.
    destruct H6.
    subst.
    rewrite <- IHis_fresh1 in H3.
    rewrite <- IHis_fresh2 in H4.
    econstructor;eauto.
  - inversion h;subst;simpl in *;clear h. 
    apply Bool.orb_true_iff in H6.
    destruct  H6;subst.
    + apply IHis_fresh1 in H3.
      destruct (interp_def_tot ψ v);eauto.
      * eapply I_Ou;eauto.
      * eapply I_Ou;eauto.
    + apply IHis_fresh2 in H4.
      destruct (interp_def_tot φ v);eauto.
      * eapply I_Ou;eauto.
      * eapply I_Ou;eauto.
  - inversion h;subst;clear h.
    apply Bool.orb_true_iff in H6.
    destruct  H6;subst.
    + rewrite <- (IHis_fresh1 _ x) in H3.
      destruct (interp_def_tot ψ (subst_in_interp v i x));eauto.
      * econstructor;eauto.
      * econstructor;eauto.
    + rewrite <- (IHis_fresh2 _ x) in H4.
      destruct (interp_def_tot φ (subst_in_interp v i x));eauto.
      * econstructor;eauto.
      * econstructor;eauto.
  - inversion h;subst;simpl in *;clear h. 
    apply implb_prop in H6.
    destruct  H6;subst.
    + apply interp_not_true in H3.
      rewrite IHis_fresh1 in H3.
      apply interp_not_true in H3.
      destruct (interp_def_tot ψ v);eauto.
      * eapply I_Implique;eauto.
      * eapply I_Implique;eauto.
    + apply IHis_fresh2 in H4.
      destruct (interp_def_tot φ v);eauto.
      * eapply I_Implique;eauto.
      * eapply I_Implique;eauto.
  - inversion h;subst;clear h.
    apply implb_prop in H6.
    destruct  H6;subst.
    + apply interp_not_true in H3.
      rewrite <- (IHis_fresh1 _ x) in H3.
      apply interp_not_true in H3.
      destruct (interp_def_tot ψ (subst_in_interp v i x));eauto.
      * econstructor;eauto.
      * econstructor;eauto.
    + rewrite <- (IHis_fresh2 _ x) in H4.
      destruct (interp_def_tot φ (subst_in_interp v i x));eauto.
      * econstructor;eauto.
      * econstructor;eauto.
  - eapply subst_fresh_id_pred;eauto.
  - eapply subst_fresh_id_pred;eauto.
  - inversion h;clear h; subst.
    constructor.
    intros x0.
    specialize (H2 x0).
    rewrite subst_permut in H2;auto.
    rewrite IHis_fresh in H2.
    assumption.
  - inversion h;clear h; subst.
    constructor.
    intros x0.
    specialize (H2 x0).
    rewrite subst_permut;auto.
    rewrite IHis_fresh.
    assumption.
  - inversion h;clear h; subst.
    constructor.
    destruct H2 as [y h].
    rewrite subst_permut in h;auto.
    rewrite IHis_fresh in h.
    exists y.
    assumption.
  - inversion h;clear h; subst.
    constructor.
    destruct H2 as [y h].
    exists y.
    rewrite subst_permut ;auto.
    rewrite IHis_fresh.
    assumption.
Qed.

(* end hide *)

(** On peut changer l'interprétation d'une variable fraîche sans
    changer l'interprétation (puisqu'elle n'appraît pas dans la
    formule). *)

Lemma subst_fresh_id: forall i φ,
                        is_fresh i φ
                        -> forall b v x, (subst_in_interp v i x) -[φ]-> b
                                         <-> v -[φ]-> b.
Proof.
  intros i φ H b v x.
  destruct b.
  - apply subst_fresh_id_true.
    assumption.
  - split;intros h;apply interp_not_true in h.
    + apply interp_not_true.
      intro abs.
      apply <- (subst_fresh_id_true i φ H v x) in abs.
      contradiction.
    + apply interp_not_true.
      intro abs.
      apply (subst_fresh_id_true i φ H v x) in abs.
      contradiction.
Qed.

(** * Substitution de variable dans une formule *)

(** On se donne une opération de substitution de variable par un terme
    dans une formule. *)

Fixpoint substtermvar (n:nat) (v:nat) (fr:formule) {struct fr}: formule :=
  match fr with
      ⊤ => ⊤
    | ⊥ => ⊥
    | Var x => Var x
    | Non x => Non (substtermvar n v x)
    | Ou x x0 => Ou (substtermvar n v x) (substtermvar n v x0)
    | Et x x0 => Et (substtermvar n v x) (substtermvar n v x0)
    | Implique x x0 => Implique (substtermvar n v x) (substtermvar n v x0)
    | (Pred i l) =>
      Pred i (List.map (fun trm' =>
                          let '(TVar v') := trm' in
                          if Nat.eqb v' n then TVar v else TVar v') l)
    | FORALL i fr' => if Nat.eqb n i || Nat.eqb v i then fr else FORALL i (substtermvar n v fr')
    | EXIST i fr' => if Nat.eqb n i || Nat.eqb v i then fr else EXIST i (substtermvar n v fr')
  end.

(* Local Notation "f [ i <= trm ]" := (substtermvar i trm f) (at level 85). *)

(** [
Eval compute in (substtermvar 1 2 (p₁[x₁,x₁,x₃])).
Eval compute in (substtermvar 1 2 (p₁[x₂,x₁,x₃])).
Eval compute in (substtermvar 1 2 (∀x₁ p₁[x₁,x₁,x₃])).
Eval compute in (substtermvar 1 3 ((∀x₁ p₁[x₁,x₁,x₃]) ∨ ∃x₃ p₁[x₁,x₁,x₃])).
Eval compute in (substtermvar 1 2 ((∀x₁ p₁[x₁,x₁,x₃]) ∨ ∃x₃ p₁[x₁,x₁,x₃])).
Eval compute in (substtermvar 1 2 ((∀x₁ p₁[x₁,x₁,x₃]) ∨ ∀x₃ p₁[x₁,x₁,x₃])). ] *)

Lemma subst_substterm_pred:
  forall n l i v var b,
    (v -[substtermvar i var (Pred n l)]-> b)
    <-> (subst_in_interp v i (vterme v (TVar var)) -[Pred n l]-> b).
Proof.
  induction l;simpl;intros;split.
  - constructor.
    simpl.
    inv H.
    reflexivity.
  - constructor.
    simpl.
    inv H.
    reflexivity.
  - constructor.
    simpl.
    inv H.
    apply f_equal.
    apply f_equal2.
    + destruct a.
      destruct (Nat.eqb n0 i);simpl;reflexivity.
    + rewrite map_map.
      apply map_ext.
      intros a0.
      destruct a0.      
      destruct (Nat.eqb n0 i);reflexivity.
  - constructor.
    simpl.
    inv H.
    apply f_equal.
    apply f_equal2.
    + destruct a.
      destruct (Nat.eqb n0 i);simpl;reflexivity.
    + rewrite map_map.
      apply map_ext.
      intros a0.
      destruct a0.      
      destruct (Nat.eqb n0 i);auto.
Qed.

Lemma substinterp_substvar_eq:
  forall i v φ var b (hfreshv:is_not_bound var φ) (hfreshi:is_not_bound i φ),
    ((v -[substtermvar i var φ]-> b) <-> (subst_in_interp v i (v.(vterme) (TVar var)) -[φ]-> b)).
Proof.
  intros i v φ.
  revert i v.
  induction φ;intros;split;intro h; try inversion hfreshv; try inversion hfreshi;subst.
  - inv h. constructor.
  - inv h. constructor.
  - inv h. constructor.
  - inv h. constructor.
  - inv h.
    constructor.
    unfold subst_in_interp.
    simpl.
    reflexivity.
  - inv h.
    constructor.
    reflexivity.
  - inv h.
    econstructor;auto.
    apply IHφ;auto.
  - inv h.
    econstructor;eauto.
    apply IHφ;auto.
  - inv h.
    econstructor;eauto.
    + apply IHφ1;auto.
    + apply IHφ2;auto.
  - inv h.
    econstructor;eauto.
    + apply IHφ1;auto.
    + apply IHφ2;auto.
  - inv h.
    econstructor;eauto.
    + apply IHφ1;auto.
    + apply IHφ2;auto.
  - inv h.
    econstructor;eauto.
    + apply IHφ1;auto.
    + apply IHφ2;auto.
  - inv h.
    econstructor;eauto.
    + apply IHφ1;auto.
    + apply IHφ2;auto.

  - inv h.
    econstructor;auto.
    + apply IHφ1;auto.
    + apply IHφ2;auto.
  - apply subst_substterm_pred.
    assumption.
  - apply subst_substterm_pred.
    assumption.
  - rename H1 into hfreshv'.
    rename H5 into hfreshi'.
    rename H2 into hvn.
    rename H6 into hin.
    simpl in h.
    rewrite (beq_nat_diff _ _ hvn) in h.
    rewrite (beq_nat_diff _ _ hin) in h.
    simpl in h.
    inv h.
    + constructor.
      intro x.
      assert (h':=H2 x).
      apply IHφ in h'.
      * rewrite subst_permut in h';auto.
        unfold subst_in_interp at 3 in h'.
        simpl in h'.
        rewrite (beq_nat_diff _ _ hvn) in h'.
        assumption.
      * inversion hfreshv.
        assumption.
      * inversion hfreshi.
        assumption.
    + constructor.
      destruct H2 as [x h'].
      apply IHφ in h'.
      * rewrite subst_permut in h';auto.
        unfold subst_in_interp at 3 in h'.
        simpl in h'.
        rewrite (beq_nat_diff _ _ hvn) in h'.
        exists x.
        assumption.
      * inversion hfreshv.
        assumption.
      * inversion hfreshi.
        assumption.
  - rename H1 into hfreshv'.
    rename H5 into hfreshi'.
    rename H2 into hvn.
    rename H6 into hin.
    simpl.
    rewrite (beq_nat_diff _ _ hvn).
    rewrite (beq_nat_diff _ _ hin).
    simpl.
    inv h.
    + constructor.
      intro x.
      assert (h':=H2 x).
      rewrite subst_permut in h';auto.

      inversion hfreshv.
      inversion hfreshi.
      specialize (IHφ i (subst_in_interp v n x) var true H1 H6).
      unfold subst_in_interp at 4 in IHφ.
      simpl in IHφ.
      rewrite (beq_nat_diff var n H3) in IHφ.
      apply IHφ.
      assumption.
    + constructor.
      destruct H2 as [x h'].
      rewrite subst_permut in h';auto.

      inversion hfreshv.
      inversion hfreshi.
      specialize (IHφ i (subst_in_interp v n x) var false H1 H5).
      unfold subst_in_interp at 4 in IHφ.
      simpl in IHφ.
      rewrite (beq_nat_diff var n H2) in IHφ.
      exists x.
      apply IHφ.
      assumption.

  - rename H1 into hfreshv'.
    rename H5 into hfreshi'.
    rename H2 into hvn.
    rename H6 into hin.
    simpl in h.
    rewrite (beq_nat_diff _ _ hvn) in h.
    rewrite (beq_nat_diff _ _ hin) in h.
    simpl in h.
    inv h.
    + constructor.
      destruct H2 as [x h'].
      apply IHφ in h'.
      * rewrite subst_permut in h';auto.
        unfold subst_in_interp at 3 in h'.
        simpl in h'.
        rewrite (beq_nat_diff _ _ hvn) in h'.
        exists x.
        assumption.
      * inversion hfreshv.
        assumption.
      * inversion hfreshi.
        assumption.
    + constructor.
      intros x.
      assert (h':=H2 x).
      apply IHφ in h'.
      * rewrite subst_permut in h';auto.
        unfold subst_in_interp at 3 in h'.
        simpl in h'.
        rewrite (beq_nat_diff _ _ hvn) in h'.
        assumption.
      * inversion hfreshv.
        assumption.
      * inversion hfreshi.
        assumption.
  - rename H1 into hfreshv'.
    rename H5 into hfreshi'.
    rename H2 into hvn.
    rename H6 into hin.
    simpl.
    rewrite (beq_nat_diff _ _ hvn).
    rewrite (beq_nat_diff _ _ hin).
    simpl.
    inv h.
    + constructor.
      destruct H2 as [x h'].
      rewrite subst_permut in h';auto.

      inversion hfreshv.
      inversion hfreshi.
      specialize (IHφ i (subst_in_interp v n x) var true H1 H5).
      unfold subst_in_interp at 4 in IHφ.
      simpl in IHφ.
      rewrite (beq_nat_diff var n H2) in IHφ.
      exists x.
      apply IHφ.
      assumption.
    + constructor.
      intro x.
      assert (h':=H2 x).
      rewrite subst_permut in h';auto.

      inversion hfreshv.
      inversion hfreshi.
      specialize (IHφ i (subst_in_interp v n x) var false H1 H6).
      unfold subst_in_interp at 4 in IHφ.
      simpl in IHφ.
      rewrite (beq_nat_diff var n H3) in IHφ.
      apply IHφ.
      assumption.
Qed.


(* Pour Forall on garde la formule intacte pour pouvoir la réutiliser
   sur d'autres instances. *)
Lemma tableau_forall :
  forall F f₁ i var,
    is_not_bound var f₁
    -> is_not_bound i f₁
    -> substtermvar i var f₁ ∧ (FORALL i f₁) ∧ F ⊧ ⊥
    -> (FORALL i f₁) ∧ F ⊧ ⊥.
Proof.
  intros F f₁ i var hfreshv hfreshi hv.
  intros v hforall.
  unfold consequence,est_modele,equiv in *.
  simp.
  - apply hv with (v:=v).
    apply I_Et with true true;try reflexivity.
    + apply substinterp_substvar_eq.
      * assumption.
      * assumption.
      * apply H5.
    + apply I_Et with true true;try reflexivity.
      * apply I_Forall. intros x. apply H5.
      * assumption.
  - discriminate.
Qed.


Lemma tableau_exist:
  forall F f₁ i j,
    is_fresh j f₁
    -> is_not_bound i f₁
    -> is_fresh j F
    -> substtermvar i j f₁ ∧ F ⊧ ⊥
    -> EXIST i f₁ ∧ F ⊧ ⊥.
Proof.
  intros F f₁ i j jfreshinf₁ ifreshinf₁ jfreshinF h.
  unfold consequence,est_modele,equiv in *.
  intros v H0.

  inv H0. 
  inversion_bool.
  subst.
  inv H2.
  destruct H0.
  exfalso.
  apply (interp_true_false ⊥ (subst_in_interp v j x)).
  + constructor.
  + apply h.
    apply I_Et with true true.
    * apply substinterp_substvar_eq.
      { apply fresh_is_not_bound;assumption. }
      { assumption. }
      unfold subst_in_interp at 3.
      simpl.
      rewrite (Nat.eqb_refl).
      { destruct (eq_nat_dec i j).
        - subst.
          assert (Interp_eq (subst_in_interp (subst_in_interp v j x) j x) (subst_in_interp v j x)).
          { unfold subst_in_interp;simpl.
            constructor;simpl;auto.
            - reflexivity.
            - intro t.
              destruct t.
              destruct (Nat.eqb n j);auto.
            - reflexivity.
          }
          rewrite H0.
          assumption.
        - rewrite (subst_permut v i j).
          + apply subst_fresh_id;auto.
          + assumption. }
    * apply subst_fresh_id;auto.
    * reflexivity.
Qed.

Lemma tableau_exist':
  forall f₁ i j,
    is_fresh j f₁
    -> is_not_bound i f₁
    -> substtermvar i j f₁ ⊧ ⊥
    -> EXIST i f₁ ⊧ ⊥.
Proof.
  intros f₁ i j jfreshinf₁ ifreshinf₁ h.
  unfold consequence,est_modele,equiv in *.
  intros v H0.

  inv H0. 
  destruct H1.
  exfalso.
  apply (interp_true_false ⊥ (subst_in_interp v j x)).
  + constructor.
  + apply h.
    apply substinterp_substvar_eq.
    { apply fresh_is_not_bound;assumption. }
    { assumption. }
    unfold subst_in_interp at 3.
    simpl.
    rewrite (Nat.eqb_refl).
    { destruct (eq_nat_dec i j).
      - subst.
        assert (Interp_eq (subst_in_interp (subst_in_interp v j x) j x) (subst_in_interp v j x)).
        { unfold subst_in_interp;simpl.
          constructor;simpl;auto.
          - reflexivity.
          - intro t.
            destruct t.
            destruct (Nat.eqb n j);auto.
          - reflexivity. }
        rewrite H0.
        assumption.
      - rewrite (subst_permut v i j).
        + apply subst_fresh_id;auto.
        + assumption. }
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
Ltac do_ferme p :=
  extrait (¬p); extrait p;
  first [apply (tableau_ferme_branche''')
        | apply tableau_ferme_branche'].
(* end hide *)
(* Ltac do_Forall P x := extrait P; apply tableau_forall with x; simpl substtermvar. *)
Ltac do_exist P n :=
  (extrait_ P;
   match goal with
     | |-  context [TVar n] => fail
     | _ =>
       (eapply tableau_exist with (j:=n)
        ;[repeat progress constructor;try lia
         |repeat progress constructor;try lia
         |repeat progress constructor;try lia
         |simpl])
   end).

Ltac do_Forall P n :=
  (extrait_ P;
   match goal with
     | |-  context [TVar n] => fail
     | _ =>
       (eapply tableau_forall with (var:=n)
        ;[repeat progress constructor;try lia
         |repeat progress constructor;try lia
         |simpl])
   end).

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

  Lemma conseq1': (X₁∨¬(p₁[x₁])) ∧ p₁[x₁] ⊧ X₁.
  Proof.
    apply conseq_by_contradiction.
    do_Ou X₁ (¬p₁[x₁]).
    - do_ferme X₁.
    - do_ferme (p₁[x₁]).
  Qed.

  Lemma conseq1'''': (∃x₁ ((X₁∨¬(p₁[x₁])) ∧ p₁[x₁]))  ⊧ X₁.
  Proof.
    apply conseq_by_contradiction.
    do_exist (∃x₁((X₁ ∨ ¬p₁[x₁]) ∧ p₁[x₁])) 9.
    do_Et ((X₁ ∨ ¬p₁ [x₉]))(p₁ [x₉]).
    do_Ou X₁ (¬p₁[x₉]).
    - do_ferme X₁.
    - do_ferme (p₁[x₉]).
  Qed.

  Lemma conseq1''':  p₁[x₃] ∧ (∃x₁ ((X₁∨¬(p₁[x₁])) ∧ p₁[x₁]))  ⊧ X₁.
  Proof.
    apply conseq_by_contradiction.
    do_exist (∃x₁((X₁ ∨ ¬p₁ [x₁]) ∧ p₁ [x₁])) 9.
    do_Et ((X₁ ∨ ¬p₁ [x₉]))(p₁ [x₉]).
    do_Ou X₁ (¬p₁[x₉]).
    - do_ferme X₁.
    - do_ferme (p₁[x₉]).
  Qed.


  Lemma conseq1'': (X₁∨¬(p₁[x₁])) ∧ (∀x₁ p₁[x₁]) ⊧ X₁.
  Proof.
    apply conseq_by_contradiction.
    do_Ou X₁ (¬p₁[x₁]).
    - do_ferme X₁.
    - do_Forall (∀x₁(p₁ [x₁])) 1.
      do_ferme (p₁[x₁]).
  Qed.

  Lemma foralneg: (¬∀x₁ p₁[x₁]) ⊧ ∃x₂ ¬p₁[x₂].
  Proof.
    apply conseq_by_contradiction.
    rewrite eq_not_exist.
    do_exist (∃x₁ ¬(p₁ [x₁])) 3.
    rewrite eq_not_forall.
    do_Forall (∀x₂(¬(¬p₁[x₂]))) 3.
    do_ferme (¬p₁[x₃]).
  Qed.

  Lemma existneg: (¬∃x₁ p₁[x₁]) ⊧ ∀x₂ ¬p₁[x₂].
  Proof.
    apply conseq_by_contradiction.
    rewrite eq_not_exist.
    do_exist (∃x₂ (¬(¬(p₁ [x₂])))) 3.
    rewrite eq_not_forall.
    do_Forall (∀x₁(¬p₁[x₁])) 3.
    do_ferme (¬p₁[x₃]).
  Qed.



  Lemma conseq2 : (X₁ ∧ X₃ ) ∧ (¬X₁ ∨ X₂) ⊧ ⊥.
  Proof.
    do_Ou (¬X₁) X₂.
    - do_ferme X₁.
    - (** Echec *)
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
    - (** Echec *)
  Abort.

End Exemple_Tableaux.
(* end show *)


Print Assumptions tableau_forall.
Print Assumptions tableau_exist.
Print Assumptions interp_def_tot.


