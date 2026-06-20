Require Import Utf8.
Require Export CoreGenericEnv.
Require Export GenericEnv.
Require Export GenericEnvList.
Require Import Morphisms.
Require Import Setoid.
Require Export Gen_env_more.
Require Import semantique.


Inductive type:Set := TBool | TInt.

Function typeof (v:value):type :=
  match v with
    | Bool x => TBool
    | Int x => TInt
  end.

(* begin hide *)
Reserved Notation "A '⊢' B '-=>' C" (at level 20, no associativity).
(* end hide  *)

Inductive Typage_exp (Γ:gen_env type):  exp -> type -> Prop :=
| Typage_Var: forall i t,
                                     Ext.binds i t Γ ->
                                     __________________
                                     Γ ⊢ VAR i -=> t
| Typage_TRUE:
                                     __________________
                                     Γ ⊢ TRUE -=> TBool
| Typage_FALSE:
                                     __________________
                                     Γ ⊢ FALSE -=> TBool
| Typage_CST: forall i,
                                     __________________
                                     Γ ⊢ CST i -=> TInt
| Typage_NOT: forall e,
                                     Γ ⊢ e -=> TBool ->
                                     __________________
                                     Γ ⊢ NOT e -=> TBool
| Typage_AND: forall e1 e2,
                                     Γ ⊢ e1 -=> TBool ->
                                     Γ ⊢ e2 -=> TBool ->
                                     __________________
                                     Γ ⊢ e1 && e2 -=> TBool
| Typage_OR: forall e1 e2,
                                     Γ ⊢ e1 -=> TBool ->
                                     Γ ⊢ e2 -=> TBool ->
                                     __________________
                                     Γ ⊢ e1 || e2 -=> TBool
| Typage_PLUS: forall e1 e2,
                                     Γ ⊢ e1 -=> TInt ->
                                     Γ ⊢ e2 -=> TInt ->
                                     __________________
                                     Γ ⊢ e1 + e2 -=> TInt
| Typage_MINUS:  forall e1 e2,
                                     Γ ⊢ e1 -=> TInt ->
                                     Γ ⊢ e2 -=> TInt ->
                                     __________________
                                     Γ ⊢ e1 - e2 -=> TInt
| Typage_MULT: forall e1 e2,
                                     Γ ⊢ e1 -=> TInt ->
                                     Γ ⊢ e2 -=> TInt ->
                                     __________________
                                     Γ ⊢ e1 * e2 -=> TInt

where  " A '⊢' B '-=>' C " := (Typage_exp A B C) : Prog_scope.

(** ** Calcul du type *)

(** On définit d'abord la fonction de test d'égalité sur les types. *)
Definition type_eq (t1 t2: type): bool:=
  match t1 with
    | TBool => match t2 with
                 | TBool => true
                 | TInt => false
               end
    | TInt =>  match t2 with
                 | TInt => true
                 | TBool => false
               end
  end.

Definition type_eq_opt (t1: option type) (t2:type): bool :=
  match t1 with
    | None => false
    | Some t => type_eq t t2
  end
.
    
(** Fonction de typage proprement dite: Retourne None si expression
    mal typée. *)
Function typage_exp (Γ:gen_env type) (e:exp): option type :=
  match e with
    | TRUE => Some TBool
    | FALSE => Some TBool
    | CST x => Some TInt
    | VAR i => ENV.Core.get i Γ
    | PLUS x y 
    | MINUS x y
    | OPP x y
    | MULT x y
    | DIV x y => if andb (type_eq_opt (typage_exp Γ x) TInt) (type_eq_opt (typage_exp Γ y) TInt)
                  then Some TInt
                  else None
    | AND x y 
    | OR x y => if andb (type_eq_opt (typage_exp Γ x) TBool) (type_eq_opt (typage_exp Γ y) TBool)
                then Some TBool
                else None
    | NOT x => if (type_eq_opt (typage_exp Γ x) TBool) then Some TBool else None
  end.

Definition Γ1 := (ENV.Core.empty type).
Definition Γ2 := (ENV.Core.single 0 TInt).

Eval compute in (typage_exp Γ1 (CST 1 + CST 2)).
Eval compute in (typage_exp Γ1 (TRUE + CST 2)).
Eval compute in (typage_exp Γ2 (VAR 0 + CST 2)).
Eval compute in (typage_exp Γ1 (VAR 0 + FALSE)).


(** Preuve de correction de la fonction par rapport à la définition du
    typage. *)

Lemma correct_typage: ∀ Γ e t, Typage_exp Γ e t -> (typage_exp Γ e = Some t).
Proof.
  intros Γ e t H.
  induction H;simpl;auto;
  first [ rewrite IHTypage_exp
        | rewrite IHTypage_exp1; rewrite IHTypage_exp2 ]; try reflexivity.
Qed.





(** La relation d'interprétation des programmes, aussi appelée la
    sémantique des programmes. Le domaine d'interprétation est
    [gen_env value] c'est-à-dire qu'un programme est interprété comme
    une fonction (partielle, certains programmes ne termine pas) des
    états (ou environnements) vers les états. *)

Inductive Wf_prog (Γ:gen_env type): prog -> Prop :=
| Wf_NOPE:
                                    __________________
                                    Wf_prog Γ NOPE
| Wf_Seq: forall p1 p2,
                                    Wf_prog Γ p1 ->
                                    Wf_prog Γ p2 ->
                                    __________________
                                    Wf_prog Γ (p1;;p2)
| Wf_Aff: forall e i (t t':type),
                                    (Γ ⊢ e -=> t) -> 
                                    Ext.binds i t' Γ ->
                                    t = t' ->
                                    __________________
                                    Wf_prog Γ (i ← e)

| Wf_If_then: forall e p1 p2,
                                    (Γ ⊢ e -=> TBool) ->
                                    Wf_prog Γ p1 -> 
                                    Wf_prog Γ p2 -> 
                                    ____________________________________
                                    Wf_prog Γ (IF e THEN p1 ELSE p2)
| Wf_While_true: forall e p,
                                    (Γ ⊢ e -=> TBool) ->
                                    Wf_prog Γ p ->
                                    ____________________________________
                                    Wf_prog Γ (WHILE e DO p DONE).

(* Definition compat1 (σ:gen_env value) (Γ:gen_env type) :=
  ∀ x t v, (Ext.binds x v σ /\ typeof v = t) -> (Ext.binds x t Γ).

Definition compat2(σ:gen_env value) (Γ:gen_env type) :=
  ∀ x t, (Ext.binds x t Γ) -> exists v, (Ext.binds x v σ /\ typeof v = t).
 *)
Definition compat (σ:gen_env value) (Γ:gen_env type) :=
  ∀ x t, (∃ v, Ext.binds x v σ /\ typeof v = t) <-> (Ext.binds x t Γ).


Add Parametric Morphism: @compat
    with signature @Ext.eq _ ==> @eq _ ==> iff as Wf_prog_morphism.
Proof.
  intros Γ1 Γ2 (heq1,heq2) p.
  unfold compat in *.
  split.
  - intros H x t.
    specialize (H x t).
    destruct H as [h h'].
    split;intros h''.
    + apply h.
      decompose [ex and] h''. clear h''.
      exists x0.
      split.
      * apply heq2.
        assumption.
      * assumption.
    + specialize (h' h'').
      decompose [ex and] h'.
      exists x0.
      split.
      * apply heq1. assumption.
      * assumption.
  - intros H x t.
    specialize (H x t).
    destruct H as [h h'].
    split;intros h''.
    + apply h.
      decompose [ex and] h''. clear h''.
      exists x0.
      split.
      * apply heq1.
        assumption.
      * assumption.
    + specialize (h' h'').
      decompose [ex and] h'.
      exists x0.
      split.
      * apply heq2. assumption.
      * assumption.
Qed.
    
        
Lemma correc_typage_exp : ∀ Γ e t,
  Γ ⊢ e -=> t -> ∀ σ, compat σ Γ -> exists v, (eval_exp σ e v /\ typeof v = t).
Proof.
  intros Γ e t H.
  induction H;intros σ comp.
  - specialize (comp i t).
    apply comp in H.
    decompose [ex and] H. clear H.
    exists x.
    split.
    + constructor. assumption.
    + assumption.
  - exists (Bool true);split;simpl;auto;constructor.
  - exists (Bool false);split;simpl;auto;constructor.
  - exists (Int i);split;simpl;auto;constructor.
  - specialize (IHTypage_exp σ comp).
    decompose [ex and] IHTypage_exp. clear IHTypage_exp.
    functional inversion H2;subst.
    exists (Bool (negb x0));split;simpl;auto.
    apply Eval_NOT with (v' := x0);auto.
  - specialize (IHTypage_exp1 σ comp).
    specialize (IHTypage_exp2 σ comp).
    decompose [ex and] IHTypage_exp1. clear IHTypage_exp1.
    decompose [ex and] IHTypage_exp2. clear IHTypage_exp2.
    functional inversion H3;subst.
    functional inversion H5;subst.
    exists (Bool (andb x1 x)).
    split.
    + apply Eval_AND with (v1 := x1) (v2:= x);auto.
    + assumption.
  - specialize (IHTypage_exp1 σ comp).
    specialize (IHTypage_exp2 σ comp).
    decompose [ex and] IHTypage_exp1. clear IHTypage_exp1.
    decompose [ex and] IHTypage_exp2. clear IHTypage_exp2.
    functional inversion H3;subst.
    functional inversion H5;subst.
    exists (Bool (orb x1 x)).
    split.
    + apply Eval_OR with (v1 := x1) (v2:= x);auto.
    + assumption.
  - specialize (IHTypage_exp1 σ comp).
    specialize (IHTypage_exp2 σ comp).
    decompose [ex and] IHTypage_exp1. clear IHTypage_exp1.
    decompose [ex and] IHTypage_exp2. clear IHTypage_exp2.
    functional inversion H3;subst.
    functional inversion H5;subst.
    exists (Int (x1 + x)).
    split.
    + apply Eval_PLUS with (v1 := x1) (v2:= x);auto.
    + assumption.
  - specialize (IHTypage_exp1 σ comp).
    specialize (IHTypage_exp2 σ comp).
    decompose [ex and] IHTypage_exp1. clear IHTypage_exp1.
    decompose [ex and] IHTypage_exp2. clear IHTypage_exp2.
    functional inversion H3;subst.
    functional inversion H5;subst.
    exists (Int (x1 - x)).
    split.
    + apply Eval_MINUS with (v1 := x1) (v2:= x);auto.
    + assumption.
  - specialize (IHTypage_exp1 σ comp).
    specialize (IHTypage_exp2 σ comp).
    decompose [ex and] IHTypage_exp1. clear IHTypage_exp1.
    decompose [ex and] IHTypage_exp2. clear IHTypage_exp2.
    functional inversion H3;subst.
    functional inversion H5;subst.
    exists (Int (x1 * x)).
    split.
    + apply Eval_MULT with (v1 := x1) (v2:= x);auto.
    + assumption.
Qed.



Lemma correc_typage_prog:
  ∀ p σ σ', 《 σ, p 》 ⟿ σ' ->  ∀ Γ, Wf_prog Γ p -> compat σ Γ -> compat σ' Γ.
Proof.
  intros p σ σ' σp_σ'.
  induction σp_σ'; intros Γ wfprog comp.
  - inversion wfprog;subst.
    rewrite <- H.
    assumption.
  - inversion wfprog;subst.
    apply IHσp_σ'2.
    + assumption.
    + apply IHσp_σ'1.
      * assumption.
      * assumption.
  - unfold compat in *.


    inversion wfprog;subst. clear wfprog.
    rewrite H0.
    unfold compat in *.
    intros x t.
    destruct (eq_keys_dec i x).
    + subst.
      split;intros .
      destruct H1 as [v' [h h']].
      assert (v=v').
      { eapply Ext.binds_eq_inv;eauto.
        apply Ext.binds_update_one_eq;auto.
        admit.
      }
      subst.
      specialize (comp x (typeof v')).
      apply comp.
      exists v'.
      

      Ext.binds_update_one_eq.


      apExt.binds_update_one_eq
      apply update_one_single.


      eapply correc_typage_exp with (Γ:=Γ) (e:=e) (t:=t') (σ:=σ) in H3.

      * apply Ext.binds_update_one_eq.


    admit. (* substitution. *)
  - inversion wfprog;subst. clear wfprog.
    auto.
  - inversion wfprog;subst. clear wfprog. auto.
  - inversion wfprog;subst. clear wfprog.
    apply IHσp_σ'2.
    + constructor;auto.
    + auto.
  - inversion wfprog;subst. clear wfprog. rewrite <- H. assumption.
Qed.



(* Local Variables: *)
(* coq-prog-name: "coqtop" *)
(* coq-load-path: ("~/enseignement/preuveprog/coq/Generic_Env_v0.3") *)
(* End: *)
