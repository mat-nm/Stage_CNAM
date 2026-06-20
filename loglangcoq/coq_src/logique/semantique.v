(* Copyright Pierre Courtieu *)
(** printing __________________ %\line(1,0){100}% #_____________<BR># *)
(** printing ____________________________________ %\line(1,0){180}% #_____________<BR># *)
(** remove printing -> *)
(** remove printing forall *)
(** remove printing exists *)
(** remove printing ~ *)
(** remove printing => *)
(** printing -> $\longrightarrow$ #&#10230;# *)
(*moche printing => $\longrightarrow$ #&#10233;# *)
(** printing << %XXXXXXXX1% *)
(** printing >> %XXXXXXXX4% *)
(** printing |-- %XXXXXXXX3% *)
(** printing ; %XXXXXXXX2% *)

(** %\chapter{Sémantique simple}%#<h1 class="libtitle">Sémantique simple</h1># *)

(** Ce module formalise la sémantique d'un petit langage impératif. Il
    n'y a pas de fonction ni de procédure.

    La sémantique d'un langage décrit formellement le comportement des
    expressions et des instructions de ce langage. C'est la
    "définition" du langage. Pour les expressions il s'agit de définir
    quelle est la valeur calculée par une expression. Pour une
    instruction il s'agit de décrire les effets des instructions sur
    les variables du programme (plus généralement les effets d'un
    programme peuvent aussi inclure les entrées/sorties mais nous ne
    considérons pas cela ici).

    La sémantique des expressions est composée de jugements de la
    forme《 σ, e 》↦ v, où σ est l'enironnement d'exécution qui
    contient les valeurs des variables du programme, e est
    l'expression à évaluer et v sa valeur.

    La sémantique des instructions sera composée de jugements de la
    forme 《 σ, p 》 ⟿ σ', où σ est l'enironnement d'exécution avant
    l'exécution du programme p et σ' est l'environnement après
    l'exécution de p. Les variables ont changé de valeur et les
    nouvelles valeur (apparaissant dans σ') sont exprimées en fonction
    des anciennes (celle de σ).

    On exprime en général cette sémantique sous la forme de règles
    d'inférence, ce qui s'écrit en Coq par une relation inductive où
    chaque constructeur correspond à une règle. *)
(* begin hide *)
Require Export GenEnv.CoreGenericEnv.
Require Export GenEnv.GenericEnv.
Require Export GenEnv.GenericEnvList.
Require Import Morphisms.
Require Import Setoid.
Require Export Gen_env_more.

Open Scope gen_env_scope.

Reserved Notation "x ;; y" (at level 70, right associativity).
(* end hide *)

(** * Les expressions *)

(** ** Le type des expressions entières et booléennes *)

Inductive exp : Set :=
| TRUE: exp
| FALSE: exp
| CST: nat -> exp
| VAR: nat -> exp
| PLUS: exp -> exp -> exp
| MINUS: exp -> exp -> exp
| OPP: exp -> exp -> exp
| MULT:  exp -> exp -> exp
| DIV:  exp -> exp -> exp
| AND:  exp -> exp -> exp
| OR:  exp -> exp -> exp
| NOT:  exp -> exp
(* TODO *)
(* | INF: exp -> exp -> exp *)
(* | SUP: exp -> exp -> exp *)
(* | EQ: exp -> exp -> exp *) 
.


(** On utilisera les notations suivante pour désigner les expressions
    de manière plus lisible. *)

Declare Scope prog_scope.
Notation "A + B" := (PLUS A B) : prog_scope.
Notation "A - B" := (MINUS A B) : prog_scope.
Notation "A * B" := (MULT A B) : prog_scope.
Notation "A / B" := (DIV A B) : prog_scope.
Notation "A && B" := (AND A B) : prog_scope.
Notation "A || B" := (OR A B) : prog_scope.
(* Notation "A < B" := (INF A B) : prog_scope. *)
(* Notation "A > B" := (SUP A B) : prog_scope. *)
(* Notation "A == B" := (EQ A B) : prog_scope. *)
Notation "! A" := (NOT A) (at level 45) : prog_scope.
Notation "'X'" := (VAR 1) (at level 0): prog_scope.
Notation "'Y'" := (VAR 2) (at level 0): prog_scope.
Notation "'Z'" := (VAR 3) (at level 0): prog_scope.
Notation "'T'" := (VAR 4) (at level 0): prog_scope.

(* begin hide *)
Open Scope prog_scope.
Reserved Notation " '《' X ',' Y '》' '↦' Z " (at level 70, no associativity).
(* end hide  *)

(** Le domaine d'interprétation des expressions est l'union de
    l'ensemble des entiers et des booléen. On utlise un type inductif
    à deux constructeurs. *)
Inductive value : Set := 
  Bool: bool -> value
| Int: nat -> value.

(** * La sémantique opérationnelle à grands pas des expressions  *)

(* begin hide *)
Notation "'__________________' P2" := (P2) (at level 90, P2 at level 200, right associativity, only parsing).
Notation "'____________________________________' P2" := (P2) (at level 90, P2 at level 200, right associativity, only parsing).
(* end hide  *)

(** La relation d'interprétation des expressions. Aussi appelée la
    sémantique des expressions. Afin de présenter la sémantique sous
    la forme de règles d'inférences, on utilise des barres
    horizontales. Ces barres n'ont pas de signification (elles sont
    ignorées par Coq) autre que celle de rappeler la forme des règles
    d'inférence. Autrement dit la propriété suivante:
[[
                                     Ext.binds i v σ ->
                                     __________________
                                     《 σ, VAR i 》↦ v
]]
est équivalente à [Ext.binds i v σ -> 《 σ, VAR i 》↦ v].

Notez que pour des raisons de simplicité on ne définit pas la
sémantique de la division. En effet cela nécessiterait de traiter le
cas de la division par zéro. *)
(* begin hide *)
(* Notation "'<<' x ';' .. ';' y '|--' z '>>'" := (x -> .. (y  -> z) ..) (at level 100,only parsing, format "'<<' x ';' .. ';' y '//' '|--' z '>>'"). *)
(* end hide *)
Inductive eval_exp (σ:gen_env value):  exp -> value -> Prop :=
| Eval_Var: forall i v,
                                     (Ext.binds i v σ) ->
                                     ____________________________________
                                       《 σ, VAR i 》↦ v
| Eval_TRUE:
                                    ____________________________________
                                      《 σ, TRUE 》 ↦ Bool true
| Eval_FALSE:
                                    ____________________________________
                                      《 σ, FALSE 》 ↦ Bool false
| Eval_CST: forall i,
                                    ____________________________________
                                      《 σ, CST i 》 ↦ Int i
| Eval_NOT: forall e v v',
                                    (《 σ , e 》 ↦ (Bool v')) -> (v = negb v') ->
                                    ____________________________________
                                            《 σ , ! e 》 ↦ Bool v
| Eval_AND: forall e1 v1 e2 v2 v,
                                      《 σ , e1 》 ↦ (Bool v1) ->
                                      《 σ , e2 》 ↦ (Bool v2) ->
                                      v = andb v1 v2 ->
                                      ____________________________________
                                        《 σ , e1 && e2 》 ↦ Bool v
| Eval_OR: forall e1 v1 e2 v2 v,
                                     《 σ , e1 》 ↦ (Bool v1) ->
                                     《 σ , e2 》 ↦ (Bool v2) ->
                                     v = orb v1 v2 ->
                                     ____________________________________
                                       《 σ , e1 || e2 》 ↦ Bool v
| Eval_PLUS: forall e1 v1 e2 v2 v,
                                    《 σ , e1 》 ↦ (Int v1) ->
                                    《 σ , e2 》 ↦ (Int v2) ->
                                    v = (v1 +v2)%nat ->
                                      ____________________________________
                                    《 σ , e1 + e2 》 ↦ Int v
| Eval_MINUS: forall e1 v1 e2 v2 v,
                                    《 σ , e1 》 ↦ (Int v1) ->
                                    《 σ , e2 》 ↦ (Int v2) ->
                                    v = (v1 - v2)%nat ->
                                    ____________________________________
                                      《 σ , e1 - e2 》 ↦ Int v
| Eval_MULT: forall e1 v1 e2 v2 v,
                                    《 σ , e1 》 ↦ (Int v1) ->
                                    《 σ , e2 》 ↦ (Int v2) ->
                                    v = (v1 * v2)%nat ->
                                    ____________________________________
                                      《 σ , e1 * e2 》 ↦ Int v

(* On ne fait pas la division car compliqué en Coq. *)

where  " '《' A ',' B '》' '↦' C " := (eval_exp A B C) : prog_scope.




(* begin hide *)
Add Parametric Morphism: (@eval_exp) with signature (@Ext.eq _) ==> (eq) ==> (eq) ==> iff as eval_exp_morph.
Proof.
  intros x y H.
  intros y0 y1.
  destruct H.
  split;intro h.
  induction h ;try solve [ econstructor; eauto ].
  induction h;try solve [ econstructor; eauto ].
Qed.
(* end hide *)

(** Exemple de jugement prouvable. *)

Lemma eval_exp1 : 《(ENV.Core.empty _)  , CST 1 + CST 2 》 ↦ Int 3.
Proof.
  apply (Eval_PLUS _ _ 1 _ 2).
  apply Eval_CST.
  apply Eval_CST.
  reflexivity.
Qed.
(* begin hide *)
(** [ Print eval_exp1. ] 
[eval_exp1 = 
Eval_PLUS (empty value) (CST 1) 1 (CST 2) 2 3 (Eval_CST (empty value) 1)
  (Eval_CST (empty value) 2) eq_refl
     : 《 empty value, CST 1 + CST 2 》 ↦ Int 3]


*)
(* end hide *)
(** Preuve du déterminisme de la sémantique des expressions. *)

Lemma determinisme_exp :
  forall σ e v, 《σ,e》 ↦ v -> forall  v', 《σ,e》 ↦ v' -> v = v'.
Proof.
  intros σ e x semv.
  induction semv; intros x' semx'.
  - inversion semx';subst.
    eapply Ext.binds_eq_inv;eauto.
  - inversion semx';subst. trivial.
  - inversion semx';subst. trivial.
  - inversion semx';subst. trivial.
  - inversion semx';subst.
    apply IHsemv in H1.
    inversion H1.
    auto.
  - inversion semx';subst.
    apply IHsemv1 in H2.
    apply IHsemv2 in H3.
    inversion H2.
    inversion H3.
    auto.
  - inversion semx';subst.
    apply IHsemv1 in H2.
    apply IHsemv2 in H3.
    inversion H2.
    inversion H3.
    auto.
  - inversion semx';subst.
    apply IHsemv1 in H2.
    apply IHsemv2 in H3.
    inversion H2.
    inversion H3.
    auto.
  - inversion semx';subst.
    apply IHsemv1 in H2.
    apply IHsemv2 in H3.
    inversion H2.
    inversion H3.
    auto.
  - inversion semx';subst.
    apply IHsemv1 in H2.
    apply IHsemv2 in H3.
    inversion H2.
    inversion H3.
    auto.
Qed.


(** * Les programmes *)

(** ** Le type des programmes *)

Inductive prog : Set :=
  NOPE: prog
| AFF: nat -> exp -> prog
| SEQ: prog -> prog -> prog
| IFTE: exp -> prog -> prog -> prog
| WHILE: exp -> prog -> prog.

(** Quelques notations pour y voir plus clair. *)

Local Notation "A ;; B" := (SEQ A B): prog_scope.
Local Notation "N ← B" := (AFF N B) (at level 66): prog_scope.
#[warnings="-notation-incompatible-prefix"]
Local Notation "'X' ← B" := (AFF 1 B) (at level 66): prog_scope.
#[warnings="-notation-incompatible-prefix"]
Local Notation "'Y' ← B" := (AFF 2 B) (at level 66): prog_scope.
#[warnings="-notation-incompatible-prefix"]
Local Notation "'Z' ← B" := (AFF 3 B) (at level 66): prog_scope.
#[warnings="-notation-incompatible-prefix"]
Local Notation "'T' ← B" := (AFF 4 B) (at level 66): prog_scope.
Local Notation "'IF' A 'THEN' B 'ELSE' C" := (IFTE A B C) (at level 200): prog_scope.
Local Notation "'WHILE' A 'DO' B 'DONE'" := (WHILE A B) (at level 71): prog_scope.

Module Ex_prog.
  (** Exemples de programme; *)

  Definition prog1:prog :=
    WHILE TRUE DO
      NOPE ;;
      X ← CST(2) + X;;
      Y ← Y + Z
    DONE.

End Ex_prog.



(* begin hide *)
Reserved Notation " '《' X ',' Y '》' '⟿' Z " (at level 70, no associativity).

(* end hide  *)

(** ** La sémantique (opérationnelle, à grands pas) des programmes *)

(** On note [E ≡ F] lorsque E et F sont deux environnements (deux
    états) équivalents (les variables ont les mêmes valeurs). *)
(* begin hide *)
Notation "E '≡' F" := (Ext.eq E F) (at level 68) : gen_env_scope.
(* end hide *)

(** La relation d'interprétation des programmes, aussi appelée la
    sémantique des programmes. Le domaine d'interprétation est
    [gen_env value] c'est-à-dire qu'un programme est interprété comme
    une fonction (partielle, certains programmes ne termine pas) des
    états (ou environnements) vers les états. *)

Inductive eval_prog : prog -> gen_env value -> gen_env value -> Prop :=
| Eval_NOPE: forall σ σ',
                                     σ ≡ σ' ->
                                     __________________
                                       《 σ, NOPE 》 ⟿ σ'
| Eval_Seq: forall σ p1 σ' p2 σ'',
                                    《 σ, p1 》 ⟿ σ' -> 《 σ', p2 》 ⟿ σ'' ->
                                    ____________________________________
                                      《 σ, p1;;p2 》 ⟿ σ''
| Eval_Aff: forall σ e i v σ',
                                    《 σ, e 》  ↦ v ->
                                    σ' ≡ σ [ i <- v] ->
                                    __________________
                                     《 σ, i ← e 》 ⟿ σ'
| Eval_If_then: forall σ e p1 p2 σ',
                                    《 σ, e 》 ↦ Bool true ->
                                    《 σ, p1 》⟿ σ' ->
                                    ____________________________________
                                                《 σ, (IF e THEN p1 ELSE p2) 》 ⟿ σ'
| Eval_If_else: forall σ e p1 p2 σ',
                                    《 σ, e 》 ↦ Bool false ->
                                    《 σ, p2 》⟿ σ' ->
                                    ____________________________________
                                                《 σ, (IF e THEN p1 ELSE p2) 》 ⟿ σ'
| Eval_While_true: forall σ e p σ' σ'',
                                    《 σ, e 》 ↦ Bool true ->
                                    《 σ, p 》 ⟿ σ' ->
                                    《 σ', WHILE e DO p DONE 》⟿ σ'' ->
                                    ____________________________________
                                    《 σ, WHILE e DO p DONE 》 ⟿ σ''

| Eval_While_false: forall σ e p σ',
                                     σ ≡ σ' ->
                                     《 σ, e 》 ↦ Bool false ->
                                     ____________________________________
                                       《 σ, WHILE e DO p DONE 》 ⟿ σ'

where  " '《' A ',' B '》' '⟿' C " := (eval_prog B A C) : prog_scope.

(* begin hide  *)
#[export] Hint Resolve Ext.eq_refl Ext.eq_sym Ext.eq_trans: genenv.


Add Parametric Morphism: (@eval_prog) with signature (eq) ==> (@Ext.eq _) ==> (@Ext.eq _) ==> iff as eval_prog_morph.
Proof.
  intros pr x y hexy E1 E2 Heq.
  split;intro h.
  - revert y hexy E2  Heq.
    induction h;intros.
    + constructor.
      rewrite H in *.
      rewrite <- hexy in *.
      assumption.

    + apply Eval_Seq with σ'.
      * apply IHh1;auto with genenv.
      * apply IHh2;auto with genenv.

    + rewrite hexy in H.
      econstructor; eauto.
      rewrite <- Heq.
      rewrite H0.
      rewrite hexy.
      reflexivity.

    + eapply Eval_If_then.
      rewrite <- hexy;auto.
      eauto.

    + eapply Eval_If_else.
      rewrite <- hexy;auto.
      eauto.

    + eapply Eval_While_true with σ'.
      rewrite <- hexy;auto.
      eauto with genenv.
      eapply IHh2;auto with genenv.

    + apply Eval_While_false;eauto with genenv.
      rewrite <- hexy;auto.

  (* Sens inverse: *)
  - revert x  hexy E1 Heq.
    induction h;intros.

    + constructor.
      rewrite hexy.
      symmetry.
      rewrite H.
      assumption.

    + apply Eval_Seq with σ'.
      * eapply IHh1;auto with genenv.
      * apply IHh2;auto with genenv.

    + rewrite <- hexy in H.
      econstructor ; eauto.
      rewrite Heq.
      rewrite H0.
      rewrite hexy.
      reflexivity.

    + eapply Eval_If_then.
      rewrite hexy;auto.
      eauto.

    + eapply Eval_If_else.
      rewrite hexy;auto.
      eauto.

    + eapply Eval_While_true with σ'.
      rewrite hexy;auto.
      eauto with genenv.
      eapply IHh2;auto with genenv.

    + apply Eval_While_false;eauto with genenv.
      rewrite hexy;auto.
Qed.

(* end hide *)

(* Preuve du déterminisme de la sémantique des programmes. *)

Lemma determinisme_prog :
  forall σ p σ', 《σ,p》 ⟿ σ' -> forall σ'', 《σ,p》 ⟿ σ'' -> σ' ≡ σ''.
Proof.
  intros σ p σ' Hσ'.
  induction Hσ'; try (rename σ'' into σaux) ; intros σ'' Hσ''.

  - inversion Hσ'';auto.
    transitivity σ;auto with genenv.

  - inversion  Hσ'';subst;eauto.
    inversion  Hσ'';subst.
    assert (σ' ≡ σ'0).
    + apply IHHσ'1;auto.
    + eapply IHHσ'2;eauto.
      rewrite H;auto.

  - inversion  Hσ'';subst.
    assert (heq: v = v0 ).
    eapply determinisme_exp;eauto.
    rewrite heq in *.
    eauto with genenv.

  - inversion  Hσ'';subst.
    apply IHHσ';auto.
    absurd (Bool false = Bool true).
    intro.
    inversion H0.
    eapply determinisme_exp;eauto.


  - inversion  Hσ'';subst.
    absurd (Bool false = Bool true).
    intro.
    inversion H0.
    eapply determinisme_exp;eauto.
    apply IHHσ';auto.

  - inversion  Hσ'';subst.
    + assert (σ' ≡ σ'0).
      { apply IHHσ'1;auto. }
      eapply IHHσ'2;eauto.
      rewrite H0;auto.
    + eapply IHHσ'2;eauto.
      absurd (Bool false = Bool true).
      intro.
      inversion H0.
      eapply determinisme_exp;eauto.

  - inversion  Hσ'';subst.
    absurd (Bool false = Bool true).
    intro.
    inversion H1.
    eapply determinisme_exp;eauto.
    eauto with genenv.
Qed.

