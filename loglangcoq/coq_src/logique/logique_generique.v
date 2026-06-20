(** remove printing -> *)
(** remove printing forall *)
(** remove printing exists *)
(** remove printing ~ *)
(** remove printing => *)
(** printing -> $\longrightarrow$ #&#10230;# *)
From Stdlib Require Import DecidableType Morphisms Setoid.
Require multiset.

(** %\chapter{Les sytèmes logiques}%
    #<h1 class="libtitle">Les sytèmes logiques</h1># *)
(** Ce chapitre décrit des notions communes à toutes les logiques
    (hormis la logique propositionnelle sans variable qui est trop
    simple). On se donne une notion de formule, de valuation et
    d'interprétation et on définit les notions suivantes:
 
- modèle
- conséquence
- équivalence
- (in)satisfiabilité
- tautologie.

On étend ensuite ces notions aux environnements, c'est-à-dire aux
(multi-)ensembles de formules. *)

(** * Les données nécessaires

  Une logique consiste en un type des formules et des notions de
  valuation et d'interprétation. *)

(* begin hide *)
Module Type Logique<: DecidableType.
(* end hide *)
  (** ** Un type des formules *)
  Parameter formule:Type. (* Pour la lisibilité on garde formule *)

  (** ** Un type des valuations *)
  Parameter valuation: Type.

  (** ** Un propriété d'interprétation
     Cette propriété prend en paramètre une valuation et attribue une
     valeur de vérité à une formule. *)
  Parameter Inline interpretation: valuation -> formule -> bool -> Prop.

  (** La seule propriété exigée est qu'une formule ne peut pas avoir
      plus d'une interprétation possible. *)
  Parameter interpretation_unique:
    forall v f b1 b2, interpretation v f b1 -> interpretation v f b2 -> b1= b2.
  (* begin hide *)
  Definition t := formule. (* même si il faut faire un synonyme pour DecidableType *)
  Parameter eq : formule -> formule -> Prop.
  Parameter eq_refl : forall x : formule, eq x x.
  Parameter eq_sym : forall x y : formule, eq x y -> eq y x.
  Parameter eq_trans : forall x y z : formule, eq x y -> eq y z -> eq x z.
  Parameter eq_dec : forall x y : formule, {eq x y} + {~ eq x y}.
  (* end hide *)
(* begin hide *)
End Logique.  
(* end hide *)


(** * Vocabulaire: modèle, conséquence logique, équivalence  *)
(* begin hide *)
Declare Scope formule_scope.
Open Scope formule_scope.
Module LogiqueDefs(F:Logique).
  Import F.
  Module Notations.
    (* end hide *)
    Reserved Notation " '⊧[[' v ']]' G" (at level 90).
    Reserved Notation "Γ '⊧{}' f" (at level 90).
    Reserved Notation " '⊧[' v ']' f" (at level 90).
    Reserved Notation "f₁ ⊧ f₂" (at level 90).
    Reserved Notation "f₁ ≡ f₂" (at level 180).
  End Notations.
  Import Notations.
  (* end hide *)

  (* CECI A ÉTÉ ABANDONNÉ, on devrait peut-être avoir une notation
     pour une formule qui s'interprète en faux.

      "On utilisera l'abus de notation suivant: [v[f]] à la place de
       [(interp_def v f)]. Attention toutefois à garder en mémoire
       qu'une valuation v ne s'applique pas à une formule mais à une
       variable, c'est la fonction [interp_def] qui permet de
       généraliser une valuation sur les variable en une interprétation
       sur les formules." *)

  (** ** modèle *)

  (** la valuation [v] est un modèle de la formule [f] si elle permet
      d'interpréter [f] en [true]. Et cela se note "⊧[[v]] f", en
      mathématique le [v] est en indice du symbole ⊧ %($_v$)% #(⊧ᵥ)#. *)

  Definition est_modele v f:= interpretation v f true.
  Notation " '⊧[' v ']' f" := (est_modele v f) : formule_scope.

  (* begin hide *)
(*   Local Open Scope logique_scope. *)
  (* end hide *)

(** ** Conséquence logique *)

(** [f₁] a pour conséquence logique [f₂] si toute valuation [v]
   rendant [f₁] vraie rend égalemet [f₂] vraie. Autrement tout modèle
   de [f₁] est aussi un modèle de [f₂]. Et cela se note f₁ ⊧ f₂. On
   peut également trouver: f₁, f₂,...,fₙ ⊧ f, qui signifie que toute
   interprétation rendant simultanément toutes les fᵢ vraies rendent
   aussi f vraie. Ce qui est donc équivalent en principe à f₁ ∧
   f₂∧...∧fₙ ⊧ f. *)

  Definition consequence f₁ f₂ := forall v, (⊧[v] f₁) -> (⊧[v] f₂).
  Notation "f₁ ⊧ f₂" := (consequence f₁ f₂) : formule_scope.

  (** ** Équivalence logique *)

  (** f₁ est équivalente à f₂ si f₁ ⊧ f₂ et f₂ ⊧ f₁. Et cela se note f₁
    ≡ f₂. *)

  Definition equiv f₁ f₂ := (f₁ ⊧ f₂) /\ (f₂ ⊧ f₁).
  Notation "f₁ ≡ f₂" := (equiv f₁ f₂) (at level 180) : formule_scope.

(* ESt-CE VRAI EN GÉNÉRAL avec une notion d'interprétation indécidable (quantificateurs)? *)
  (* Une autre définition pour l'équivalence: l'interprétation des deux
    formule est toujours identique. *)
(*
  Definition equivalent p1 p2 := forall (v:valuation) b,
                                   (interpretation v p1 b)<->(interpretation v p2 b). 

  (** Preuve d'equivalence entre equiv et equivalence. *)

  Lemma equivEquivalence :forall p1 p2,(equiv p1 p2) <-> (equivalent p1 p2).
    unfold equivalent, equiv, consequence, est_modele.
    intros p1 p2.
    split.
    - intros [h1 h2] I b.
      specialize (h1 I).
      specialize (h2 I).
      destruct b.
      + split;auto.
      + split.
        * intros H.
          ????
          apply interpretation_unique in H.
          apply f_equal2;auto.
      
      destruct (I[p2]). ;destruct (interp_def I p1);auto;try discriminate.
      discriminate h1.
      reflexivity.
    - intros h.
      split; intros I h'; eauto.
  Qed.
*)
  (** ** Tautologie, formule satisfaisable, insatisfaisable... *)
  
  (** Une formule vraie dans toute interprétation est une tautologie, ou
      formule valide. *)

  Definition tautologie (f₁:formule) := forall v,  ⊧[v] f₁. 
  Notation valide := tautologie (only parsing).

  (** Une formule pour laquelle il existe un modèle est dite satifiable,
      satisfaisable ou réalisable. *)

  Definition satisfiable (f₁:formule) := exists v, ⊧[v] f₁.
  Notation realisable := satisfiable (only parsing).

  (** Si une telle interprétation n'existe pas, c'est-à-dire si la
    formule est fausse dans toute interprétation, elle est dite
    insatisfiable, insatisfaisable, ou encore on dit que c'est une
    antilogie. *)
  (* ?? equivalent à: ~(⊧[v] f₁)?? *)

  Definition insatisfiable (f₁:formule) := forall v, interpretation v f₁ false. 
  Notation antilogie := insatisfiable (only parsing).
(* begin hide *)
End LogiqueDefs.  
(* end hide *)

(** * Environnements  *)

(** Cette partie définit la notion _d'environnement_ c'est-à-dire un
    ensemble de formule (plus exactement un multi-ensemble: la même
    formule peut apparaître plusieurs fois. Cette notion sera utilisée
    par exemple pour la définition de la déduction naturelle, où les
    jugements sont de la forme Γ ⊢ φ, où Γ est un environnement et φ
    une formule. On définit les notions de modèle, conséquence,
    satisfiabilité et insatisfiabilité pour un ensemble de formules. *)
(* begin hide *)
Module Environnement(F:Logique).
(* end hide *)
  (* begin hide *)
  Module Import DEFS := LogiqueDefs(F). (* Importe aussi les notations. *)
  Import DEFS.Notations.
(* Open Scope logique_scope. *)
  (* end hide *)

  Module ENV := multiset.MakeList(F).

  (** Un environnement est un multi-ensemble de formules. *)

  Definition env := ENV.t.
  (* begin hide *)

  Local Notation formule := (F.formule).

  Add Relation ENV.t ENV.eq
      reflexivity proved by ENV.eq_refl
      symmetry proved by ENV.eq_sym
      transitivity proved by ENV.eq_trans as eq_rel.
  
  (* On peut réécrire à l'intérieur d'un ::. *)
  Add Morphism ENV.add with signature (F.eq ==> ENV.eq ==> ENV.eq)
                         as add_morph.
  Proof.
    exact ENV.add_morph_eq.
  Qed.
  
  Add Relation formule F.eq
      reflexivity proved by F.eq_refl
      symmetry proved by F.eq_sym
      transitivity proved by F.eq_trans
        as fo_eq_rel.

  (* On peut réécrire à l'intérieur d'une union d'environnements. *)
  Add Morphism ENV.union with signature (ENV.eq==> ENV.eq ==> ENV.eq)
                           as union_morph.
  Proof.
    exact ENV.union_morph_eq.
  Qed.

  (* On peut réécrire à l'intérieur d'un mem. *)
  Add Morphism ENV.mem with signature ( Logic.eq ==> ENV.eq ==> Logic.eq)
                         as mem_morph.
  Proof.
    apply ENV.mem_morph_eq.
  Qed.

  (* end hide *)

  (** ** modèle *)

  Definition est_modele_set v Γ := forall f, ENV.In f Γ -> ⊧[v] f.
  Notation " '⊧[[' v ']]' G" := (est_modele_set v G).

  (** ** conséquence *)

  Definition consequence_set (Γ: env) f₂ := forall v, ⊧[[ v ]] Γ -> ⊧[v] f₂.
  Notation "Γ '⊧{}' f" := (consequence_set Γ f).

  (** ** (in)Satisfiabilité  *)

  Definition satisfiable_set Γ := exists v, ⊧[[v]] Γ.
  Definition insatisfiable_set Γ := forall v, ~(⊧[v] Γ). 

  (** Un modèle d'une ensemble Γ de formules est également un modèle
      d'un sous-ensemble de Γ. *)

  Lemma est_model_set_subset: forall v φ Γ, ⊧[[v]] (ENV.add φ Γ) ->  ⊧[[v]] Γ.
  Proof.
    intros v φ Γ H.
    intros φ' h'.
    apply H.
    destruct (F.eq_dec φ' φ).
    - subst.
      apply ENV.in_add_eq.
      assumption.
    - apply <- ENV.in_add_neq;auto. 
  Qed.

(* begin hide *)
End Environnement. 
(* end hide *)
