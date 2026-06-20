(** %\chapter{Calcul des Séquents}%
    #<h1 class="libtitle">Calcul des Séquents</h1># *)
(** Ce module définit le système de preuve du calcul des séquents
    pour la logique propositionnelle. Il établit les propriétés
    suivantes de ce système:
    - traduction des preuves de ce système vers celui de la déduction
      naturelle. *)

(* begin hide *)

Require Import especialize.
Open Scope specialize_scope.


Check (# ! §).
From Stdlib Require Import DecidableType Morphisms FunInd Setoid EqNat Wf_nat Arith Lia.
(* Require Import multiset tables_de_verite logique_propositionnelle_avec_variables. *)
Require Import multiset tables_de_verite.
Require Import logique_propositionnelle_avec_variables.
Import logique_propositionnelle_avec_variables.Notations.
Import logique_propositionnelle_avec_variables.LogPropVarEnv.ENV.
Import logique_propositionnelle_avec_variables.LogPropVarEnv.DEFS.
Import logique_propositionnelle_avec_variables.LogPropVarEnv.


(* end hide *)
Require logique_generique.
Require deduction_naturelle.
Module DN := deduction_naturelle.
Implicit Types φ ψ φ₁ φ₂ φ₃: formule.
Implicit Types Γ Δ Ω: env.

Local Reserved Notation "X ⊢ Y" (at level 90).
Local Open Scope formule_scope.
Declare Scope formule_set_scope.
Open Scope formule_set_scope.
(** On redéfinit la notiation ⊧ pour correspondre à la conséquence
    logique entre un _ensemble_ de formule [Γ] et une formule [f].
    Dans les développement précédents f₁ ⊧ f₂ correspondait à la
    conséquence logique entre deux formule. *)
Notation "Γ ⊧ f" := (consequence_set Γ f): formule_set_scope.

Inductive pf : env -> env -> Prop :=
  eqEnv : forall Γ Γ' Δ Δ', Γ == Γ' -> Δ == Δ' -> Γ ⊢ Δ -> Γ' ⊢ Δ'
| ax : forall Γ, ~ Empty Γ -> Γ ⊢ Γ (* Dans l'original: {φ}⊢{φ} *)
| lw : forall Γ Δ φ, Γ ⊢ Δ -> φ :: Γ ⊢ Δ
| rw : forall Γ Δ φ, Γ ⊢ Δ -> Γ ⊢ φ :: Δ
| lc : forall Γ Δ φ, φ :: φ :: Γ ⊢ Δ -> φ :: Γ ⊢ Δ
| rc : forall Γ Δ φ, Γ ⊢ φ :: φ :: Δ -> Γ ⊢ φ :: Δ
| lnot : forall Γ Δ φ, Γ ⊢ φ :: Δ -> (¬ φ) :: Γ ⊢ Δ
| rnot : forall Γ Δ φ, φ :: Γ ⊢ Δ -> Γ ⊢ (¬ φ) :: Δ
| l1and : forall Γ Δ φ ψ, φ :: Γ ⊢ Δ -> (φ ∧ ψ) :: Γ ⊢ Δ
| l2and : forall Γ Δ φ ψ, ψ :: Γ ⊢ Δ -> (φ ∧ ψ) :: Γ ⊢ Δ
| rand : forall Γ Δ Γ' Δ' φ ψ,
    Γ ⊢ φ :: Δ -> Γ' ⊢ ψ :: Δ -> Γ ∪ Γ' ⊢ (φ ∧ ψ) :: (Δ ∪ Δ')
| lor : forall Γ Δ Γ' Δ' φ ψ,
    φ :: Γ ⊢ Δ -> ψ :: Γ' ⊢ Δ' -> (φ ∨ ψ) :: (Γ ∪ Γ') ⊢ Δ ∪ Δ'
| r1or : forall Γ Δ φ ψ, Γ ⊢ φ :: Δ -> Γ ⊢ (φ ∨ ψ) :: Δ
| r2or : forall Γ Δ φ ψ, Γ ⊢ ψ :: Δ -> Γ ⊢ (φ ∨ ψ) :: Δ
| limp : forall Γ Δ Γ' Δ' φ ψ,
    Γ ⊢ φ :: Δ -> ψ :: Γ' ⊢ Δ' -> (φ ⇒ ψ) :: (Γ ∪ Γ') ⊢ Δ ∪ Δ'
| rimp : forall Γ Δ φ ψ, φ :: Γ ⊢ ψ :: Δ -> Γ ⊢ (φ ⇒ ψ) :: Δ
where " X ⊢ Y" := (pf X Y).

Instance pf_compat: Proper (ENV.eq ==> ENV.eq ==> iff) pf.
Proof.
  repeat red.
  intros.
  split.
  - now apply eqEnv. 
  - now apply eqEnv.
Qed.

Lemma lc_eq : forall a A B, a ∈ A -> a :: A ⊢ B -> A ⊢ B.
Proof.
  intros.
  rewrite <- (remove_same_add_in a a A).
  - apply lc.
    rewrite remove_same_add_in.
    auto.
    + reflexivity.
    + auto.
  - reflexivity.
  - auto. 
Qed.

Lemma rc_eq : forall A b B, b ∈ B -> A ⊢ b :: B -> A ⊢ B.
Proof.
  intros.
  rewrite <- (remove_same_add_in b b B).
  - apply rc.
    rewrite remove_same_add_in.
    auto.
    + reflexivity.
    + auto.
  - reflexivity.
  - auto.
Qed.

Lemma Empty_add: forall e E, ~Empty (add e E).
Proof.
  intros e E H. 
  rewrite -> Empty_no_mem in H.
  apply (H e).
  apply in_add_eq.
  reflexivity.
Qed.

Local Notation "X '⊢dn' Y" := (DN.pf X Y) (at level 90). 
Lemma rimp_ok: forall φ φ' ψ Γ, ψ::Γ ⊢dn (φ∨φ') -> Γ ⊢dn (ψ⇒φ) ∨ φ' .
Proof.
  intros φ φ' ψ Γ h_dn. 
  assert (Γ ⊢dn ψ ∨ ¬ψ) as h_dec_ψ.
  { apply DN.Exemple_DN.a_or_nota. }
  apply DN.ore with (1:=h_dec_ψ).
  - specialize DN.ore with (1:=h_dn) (φ₃:=(ψ ⇒ φ)∨φ') as h.
    especialize h at (#§).
    especialize h at (§).
    { apply DN.ori1.
      apply DN.impi.
      DN.tax. }
    (* assert (φ' :: ψ :: Γ ⊢dn (ψ ⇒ φ) ∨ φ') as hyp2. *)    
    especialize h at (§).
    { apply DN.ori2.
      DN.tax. }
    apply h;auto.
  - apply DN.ori1.
    apply DN.impi.
    apply DN.note with (φ₁:=ψ).
    + DN.tax.
    + DN.tax.
Qed.

Lemma lk_empty_false: forall A φ, pf A (empty) -> pf A ([φ]).
Proof.
    intros.
    apply rw.
    assumption.
Qed.

Inductive is_ms_disj: formule -> env -> Prop :=
| Cdisj_false: forall Γ, Γ == ∅ -> is_ms_disj ⊥ Γ
| Cdisj_single: forall (φ:formule) Γ, Γ == [φ] -> is_ms_disj φ Γ
| Cdisj_union: forall f f' Δ Γ Γ',
    Δ == union Γ Γ' -> is_ms_disj f Γ -> is_ms_disj f' Γ' ->  is_ms_disj (f∨f') Δ.


Ltac addunion :=
  match goal with
    |- context [ is_ms_disj _ (?c :: ?e) ] => change (c :: e) with ([c]∪e)
  | |- context [ is_ms_disj _ ((?c :: ?e) ∪ ?e2) ] =>
      setoid_rewrite (union_rec_left c e e2); change (c :: (e ∪ e2)) with ([c]∪(e∪e2))
  end.
Ltac addunionh h :=
  match goal with
    H: context [ is_ms_disj _ (?c :: ?e) ] |-_ => change (c :: e) with ([c]∪e) in H
  | H: context [ is_ms_disj _ ((?c :: ?e) ∪ ?e2) ] |- _ =>
      setoid_rewrite (union_rec_left c e e2) in H; change (c :: (e ∪ e2)) with ([c]∪(e∪e2)) in H
  end.


Lemma is_ms_disj_false: forall Γ, is_ms_disj ⊥ Γ -> Γ == [⊥] \/ Γ == ∅.
Proof.
  intros Γ.
  intro h.
  inversion h;auto.
Qed.

Lemma Cdisj_single': forall φ , is_ms_disj φ ([φ]).
Proof.
  econstructor 2.
  reflexivity.  
Qed.

Local Ltac myauto := (try apply Cdisj_single');(try constructor 1);try easy.

Instance ms_disj_compat: Proper (Logic.eq ==> ENV.eq ==> iff) is_ms_disj.
Proof.
  intros φ φ' heq Γ Γ' heqEnv.
  split;intros.
  - revert φ' heq Γ' heqEnv.
    induction H;intros.
    + subst.
      rewrite H in heqEnv.
      myauto.
    + constructor 2.
      rewrite <-heq.
      now transitivity Γ.
    + subst φ'.
      econstructor 3 with (Γ:=Γ)(Γ':=Γ');eauto.
      now transitivity Δ.
  - revert φ heq Γ heqEnv.
    induction H;intros.
    + subst. 
      rewrite H in heqEnv.
      myauto.
    + constructor 2.
      * rewrite heq.
        now transitivity Γ.
    + subst φ.
      econstructor 3 with (Γ:=Γ) (Γ':=Γ').
      * now transitivity Δ.
      * assumption.
      * now apply IHis_ms_disj2.
Qed.

Lemma Cdisj_union' f Γ f' Γ': is_ms_disj f Γ -> is_ms_disj f' Γ' -> is_ms_disj (f ∨ f') (Γ∪Γ').
  econstructor 3;[reflexivity|..];auto.
Qed.

Lemma is_ms_disj_commut: forall φ φ' Γ,
    is_ms_disj (φ∨φ') Γ ->
    exists Γ', is_ms_disj (φ∨φ') Γ' /\ is_ms_disj (φ'∨φ) Γ'.
Proof.
  intros φ φ' Γ H.
  exists ([φ] ∪ [φ']).
  split.
  - apply Cdisj_union';myauto.
  - rewrite union_sym.
    apply Cdisj_union';myauto.
Qed.

Lemma is_ms_disj_assoc: forall φ φ' φ'' Γ,
    is_ms_disj (φ∨φ'∨φ'') Γ ->
    exists Γ', is_ms_disj (φ∨φ'∨φ'') Γ' /\ is_ms_disj ((φ∨φ') ∨ φ'') Γ'.
Proof.
  intros φ φ' φ'' Γ H.
  exists ([φ,φ',φ'']).
  split.
  - apply Cdisj_union' with (Γ:=[φ])(Γ':=[φ',φ'']);myauto.
    apply Cdisj_union' with (Γ:=[φ'])(Γ':=[φ'']);myauto.
  - econstructor 3 with (Γ:=[φ,φ'])(Γ':=[φ'']);myauto.
    + rewrite union_rec_left.
      reflexivity.
    + apply Cdisj_union' with (Γ:=[φ])(Γ':=[φ']);myauto.
Qed.

Lemma Cdisj_add: forall f f' Γ Γ', Γ == add f Γ' -> is_ms_disj f' Γ' ->  is_ms_disj (f∨f') Γ.
Proof.
  intros f f' Γ Γ' H H0. 
  rewrite H.
  apply Cdisj_union' with (Γ:= [f])(Γ':=Γ') ;myauto;auto.
Qed.


Lemma is_ms_disj_notempty:forall φ Γ, Γ == ∅ -> is_ms_disj φ Γ -> φ ≡ ⊥.
Proof.
  intros φ Γ Heqe. 
  intro abs.
  revert Heqe.
  induction abs;intros.
  - reflexivity.
  - exfalso.
    absurd (φ∈Γ).
    + rewrite Heqe.
      rewrite empty_in_iff.
      intro;contradiction.
    + rewrite H.
      apply in_add_eq.
      reflexivity.
  - symmetry in H.
    rewrite Heqe in H.
    apply union_empty_decompose in H.
    destruct H.
    rewrite IHabs1, IHabs2;auto.
    apply Ou_Faux.
Qed.

Lemma is_ms_disj_emptynot:forall Γ, exists φ, is_ms_disj φ Γ.
Proof.
  intros Γ. 
  induction Γ using multiset_ind.
  - setoid_rewrite <- H.
    assumption.
  - exists ⊥;myauto.
  - destruct IHΓ.
    exists (x∨x0).
    change (x::Γ) with ([x]∪ Γ).
    eapply Cdisj_union';myauto.
Qed.


Lemma disj_or: forall φ cd c d B,
    cd == (c ∨ d) :: B
    -> is_ms_disj φ cd
    -> is_ms_disj φ (c :: d :: B).
Proof.
  intros φ cd c d B Heqcd h.
  revert c d B Heqcd.
  induction h;intros.
  - exfalso.
    rewrite H in Heqcd.
    now apply (empty_add (c ∨ d) B).
  - rewrite Heqcd in H.
    apply dec_singleton in H.
    destruct H.
    rewrite H.
    red in H0.
    subst φ.
    apply Cdisj_union' with (Γ:=[c])(Γ':=[d]);myauto.
  - rewrite Heqcd in H.
    assert ((exists B' B'', Γ == (c ∨ d) :: B' /\ Γ' == B'' /\ B == B' ∪ B'')
           \/ (exists B' B'', Γ == B' /\ Γ' == (c ∨ d) :: B'' /\ B == B' ∪ B'')) as hdec.
    { symmetry in H.
      apply union_decompose in H.
      destruct H as [ [Δ' [hΓ hΓ' ] ] | [Δ' [hΓ hΓ' ] ] ].
      - left.
        exists Δ'.
        exists Γ'.
        split;auto.
        now split.
      - right.
        exists Γ.
        exists Δ'.
        split.
        { reflexivity. }
        split.
        + assumption.
        + symmetry.
          rewrite union_sym.
          assumption. }
    destruct hdec as [[B' [B'' [ hΓ [hΓ' hunion] ] ] ] | [B' [B'' [ hΓ [hΓ' hunion] ] ] ] ].
    + rewrite hunion.
      rewrite <- union_rec_left.
      rewrite <- union_rec_left.
      apply Cdisj_union';auto.
      rewrite hΓ' in h2.
      apply h2.
    + rewrite hunion.
      rewrite <- union_rec_right.
      rewrite <- union_rec_right.
      apply Cdisj_union';auto.
      rewrite hΓ in h1.
      apply h1.
Qed.



Lemma is_ms_disj_singleton: forall φ Γ, is_ms_disj φ Γ -> forall φ', Γ == ([φ']) -> φ ≡ φ'.
Proof.
  intros φ Γ H.
  induction H;intros.
  - exfalso.
    apply (empty_add φ' ∅).
    transitivity Γ.
    + now symmetry.
    + assumption.
  - rewrite H in H0.
    apply singleton_eq in H0.
    rewrite H0.
    reflexivity.
  - rewrite H2 in H.
    symmetry in H.
    apply union_singleton_decompose in H.
    destruct H as [ [hΓ hΓ'] | [hΓ hΓ'] ].
    + rewrite (IHis_ms_disj1 _ hΓ).
      apply is_ms_disj_notempty in H1;auto.
      rewrite H1.
      rewrite Ou_comm.
      rewrite Ou_Faux.
      reflexivity.
    + rewrite (IHis_ms_disj2 _ hΓ).
      apply is_ms_disj_notempty in H0;auto.
      rewrite H0.
      rewrite Ou_Faux.
      reflexivity.
Qed.




Lemma inversion_disj_union_equiv: forall Γ φ,
    is_ms_disj φ Γ ->
    forall Γ' Γ'',
      Γ == Γ'∪Γ'' ->
      exists ψ ψ',
        (φ ≡ (ψ ∨ ψ')) /\ is_ms_disj ψ Γ' /\ is_ms_disj ψ' Γ''.
Proof.
  intros Γ φ h.
  induction h.
  - intros Γ' Γ'' H0. 
    exists ⊥,⊥;split;[|split].
    + now rewrite Ou_Faux.
    + apply Cdisj_false.
      rewrite H in H0.
      symmetry in H0.
      now apply union_empty_decompose in H0.
    + apply Cdisj_false.
      rewrite H in H0.
      symmetry in H0.
      now apply union_empty_decompose in H0.
  - intros Γ' Γ'' H0.
    rewrite H0 in H.
    apply union_singleton_decompose in H.
    destruct H as [[hΓ' hΓ''] | [hΓ'' hΓ'] ].
    + exists φ, ⊥;split;[|split].
      * symmetry. apply Ou_Faux.
      * rewrite hΓ';myauto.
      * rewrite hΓ'';myauto.
    + exists ⊥, φ;split;[|split].
      * symmetry. apply Ou_Faux.
      * rewrite hΓ';myauto.
      * rewrite hΓ'';myauto.
  - intros Γ'' Γ''' hΔ.
    assert (exists Γ₁ Γ₂ Γ'₁ Γ'₂,
                 Γ == Γ₁ ∪ Γ₂ /\
                 Γ' == Γ'₁ ∪ Γ'₂ /\
                 Γ₁ ∪ Γ'₁ == Γ'' /\
                 Γ₂ ∪ Γ'₂ == Γ''') as hex.
    { symmetry in hΔ.
      specialize (union_union_decomp _ _ _ hΔ _ _ H) as h.
      decompose [ex and] h. clear h.
      exists x,x0.
      exists x1, x2.
      intuition auto with *. }
    destruct hex as [ ψ1 [ψ2 [ψ3 [φ4 [hΓ [hΓ' [hΓ'' hΓ'''] ] ] ] ] ] ].
    specialize IHh1 with (1:=hΓ).
    specialize IHh2 with (1:=hΓ').

    destruct IHh1 as [ ψ5 [ψ6 [hf [hdisjψ5 hdisjψ6] ] ] ].
    destruct IHh2 as [ ψ7 [ψ8 [hf' [hdisjψ7 hdisjψ8] ] ] ].
    (* exists (Γ'' ∪ Γ'''). *)
    exists (ψ5 ∨ ψ7).
    exists (ψ6 ∨ ψ8).
    split;[|repeat split].
    + rewrite <- Ou_assoc.
      setoid_rewrite (Ou_comm ψ7).
      rewrite <- Ou_assoc.
      rewrite Ou_assoc.
      rewrite (Ou_comm ψ8).
      rewrite <- hf',  <-hf.
      reflexivity.
    + rewrite <- hΓ''.
      apply Cdisj_union';auto.
    + rewrite <- hΓ'''.
      apply Cdisj_union';auto.
Qed.


Lemma inversion_disj_union: forall φ Γ Γ',
    is_ms_disj φ (Γ∪Γ') ->
    exists ψ ψ', (φ ≡ (ψ ∨ ψ')) /\ is_ms_disj ψ Γ /\ is_ms_disj ψ' Γ' (*/\ is_ms_disj φ Δ*).
Proof.
  intros φ Γ Γ' H. 
  eapply inversion_disj_union_equiv in H.
  2:{ reflexivity. }
  assumption.
Qed.

Lemma is_ms_disj_dn: forall ψ Γ, is_ms_disj ψ Γ -> ~Empty Γ -> Γ ⊢dn ψ.
Proof.
  intros ψ Γ H. 
  induction H as [? hempty | ? ? hsingl | ? ? ? ? ? hΔ hf ? hf' ?];intros hnotempty.
  - exfalso.
    apply hnotempty.
    rewrite hempty.
    apply Empty_empty.
  - rewrite hsingl.
    DN.tax.
  - assert (~Empty Γ \/ ~Empty Γ') as hdec.
    { rewrite hΔ in hnotempty.
      destruct (env_decomp Γ) as [h|h]; destruct (env_decomp Γ') as [h'|h'].
      - exfalso.
        rewrite h,h' in hnotempty.
        rewrite union_empty_right in hnotempty.
        apply hnotempty.
        apply Empty_empty.
      - right.
        destruct h' as [ψ [ Γ'' heq ] ].
        rewrite heq.
        apply Empty_add.
      - left.
        destruct h as [ψ [ Γ'' heq ] ].
        rewrite heq.
        apply Empty_add.
      - left.
        destruct h as [ψ [ Γ'' heq ] ].
        rewrite heq.
        apply Empty_add. }
    rewrite hΔ.
    destruct hdec.
    + apply DN.ori1.
      rewrite union_sym.
      apply DN.weakening_env.
      auto.
    + apply DN.ori2.
      apply DN.weakening_env.
      auto.
Qed.

Theorem trad_lk_dn_full: forall A B φ, A ⊢ B -> forall B', is_ms_disj φ (B∪B') -> A ⊢dn φ.
Proof.
    intros A B φ H.
    revert φ.
    induction H;intros.
    - (* 1 *)
      setoid_rewrite <- H.
      setoid_rewrite H0 in IHpf.
      apply IHpf with (1:=H2).
    - (* 2 *)
      apply inversion_disj_union in H0.
      destruct H0 as [ψ [ψ' [hperm  [ hψ hψ' (* [ hψ' hΔ ] *) ] ] ] ].
      + rewrite hperm.
        apply DN.ori1.
        apply is_ms_disj_dn.
        * assumption.
        * assumption.
    - (* 3 *) apply DN.weakening.
      apply IHpf with (1:=H0).
    - (* 4 *) rewrite union_rec_left in H0.
      rewrite <- union_rec_right in H0.
      specialize IHpf with (1:= H0).
      assumption.
    - (* 5 *) specialize IHpf with (1:= H0).
      eapply DN.contraction (*with (φ:=φ0) (Γ:=φ::Δ)*) in IHpf ; try eauto;try easy.
      now apply in_add_eq.
    - (* 6 *) 
      eapply DN.ore with (φ₁:=φ)(φ₂:=φ0).
      + apply IHpf with (B':=B').
        addunion.
        apply Cdisj_union';myauto.
      + addunionh H0.
        apply inversion_disj_union in H0.
        destruct H0 as [ψ [ψ' [hperm  [ hψ hψ' (* [ hψ' hΔ ] *) ] ] ] ].
        (* apply inversion_disj_union in H0. *)
        (* destruct H0 as [ψ [ψ' [hperm  [ hψ hψ' ] ] ] ]. *)
        rewrite hperm.
        apply DN.ori1.
        assert (φ≡ψ) as heq.
        { specialize is_ms_disj_singleton with (1:=hψ)(φ':=φ) as h.
          rewrite h.
          - reflexivity.
          - reflexivity. }
        rewrite <- heq.
        DN.tax.
      + DN.tax.
    - (* 7 *) 
      assert (is_ms_disj (φ∨φ0) (φ :: Δ ∪ B')).
      { assert ((φ :: Δ ∪ B') == ([φ] ∪ (Δ ∪ B'))) as h.
        { rewrite union_rec_left.
          reflexivity. }
        rewrite h.
        apply Cdisj_union';myauto. }
    eapply DN.ore with (φ₁:=φ)(φ₂:=φ0).
      + specialize IHpf with (B':=B').
        eapply DN.weakening with (φ:=¬ φ) (ψ:=(φ ∨ φ0)) in IHpf.
        * assumption.
        * assumption.
      + specialize IHpf with (B':=B').
        (* il y a c et ¬c dans Γ, donc on peut prouver n'importe quoi. *)
        apply DN.note with (φ₁:=φ).
        * DN.tax.
        * DN.tax.
      + DN.tax.
    - rewrite union_rec_left in H0.
      addunionh H0.
      apply inversion_disj_union in H0.
      destruct H0 as [ψ [ψ' [hperm  [ hψ hψ'(* [ hψ' hΔ ] *) ] ] ] ].
      (* apply inversion_disj_union in H0. *)
      (* destruct H0 as [ψ [ψ' [hperm  [ hψ hψ' ] ] ] ]. *)
      specialize (IHpf ψ' B' hψ').
      specialize is_ms_disj_singleton with (1:=hψ) (φ':=¬φ)  as h.
      rewrite h in hperm;try easy.
      rewrite hperm.
      eapply DN.ore with (φ₁:=φ)(φ₂:=¬φ).
      * apply DN.Exemple_DN.a_or_nota.
      * apply DN.ori2.
        assumption.
      * apply DN.ori1.
        DN.tax.
    - (* 9 *)
      specialize IHpf with (1:=H0).
      apply DN.impe with (φ₁:=φ).
      + eapply DN.impi.
        rewrite add_comm.
        apply DN.weakening.
        assumption.
      + apply DN.ande1 with (φ₂:=ψ).
        DN.tax.
    - (* 10 *)
      specialize IHpf with (1:=H0).
      apply DN.impe with (φ₁:=ψ).
      + eapply DN.impi.
        rewrite add_comm.
        apply DN.weakening.
        assumption.
      + apply DN.ande2 with (φ₁:=φ).
        DN.tax.
    - (* 11 *)
      specialize (IHpf1 (φ ∨ φ0) ((φ ∧ ψ) :: (Δ' ∪ B'))).
      specialize (IHpf2 (ψ ∨ φ0) ((φ ∧ ψ) :: (Δ' ∪ B'))).
      especialize IHpf1 at (§).
      { rewrite union_rec_left in H1.
        rewrite <- union_assoc in H1.
        rewrite union_rec_left.
        rewrite union_rec_right.
        addunion.
        apply Cdisj_union';myauto. }
      especialize IHpf2 at (§).
      { rewrite union_rec_left in H1.
        rewrite <- union_assoc in H1.
        rewrite union_rec_left.
        rewrite union_rec_right.
        addunion.
        apply Cdisj_union';myauto. }
      clear H H0.
      rewrite union_rec_left in H1.
      addunionh H1.
      apply inversion_disj_union in H1.
      destruct H1 as [f [f' [hperm  [ hf hf'(* [ hψ' hΔ ] *) ] ] ] ].
      (* apply inversion_disj_union in H1. *)
      (* destruct H1 as [ψ [ψ' [hperm  [ hψ hψ' ] ] ] ]. *)
      apply is_ms_disj_singleton with (φ':=φ ∧ ψ)(2:=eq_refl _) in hf;auto.
      rewrite hperm in *|-*.
      clear hperm (*φ*).
      rewrite hf in *|-*.
      clear hf f.
      eapply DN.ore with (φ₁:=φ) (φ₂:=φ ∧ ψ ∨ f').
      + rewrite union_sym.
        now apply DN.weakening_env.
      + eapply DN.ore with (φ₁:=ψ) (φ₂:=φ ∧ ψ ∨ f').
        * apply DN.weakening.
          now apply DN.weakening_env.
        * apply DN.ori1.
          apply DN.andi.
          -- DN.tax.
          -- DN.tax.
        * DN.tax.
      + DN.tax.
    - (* 12 *)
      specialize (IHpf1 φ0 (Δ' ∪ B')).
      specialize (IHpf2 φ0 (Δ ∪ B')).
      especialize IHpf2 at (§).
      { setoid_rewrite union_sym at 2 in H1.
        rewrite <- union_assoc in H1.
        assumption. }
      especialize IHpf1 at (§).
      { rewrite <- union_assoc in H1.
        assumption. }
      eapply DN.ore with (φ₁:=φ) (φ₂:=ψ).
      + DN.tax.
      + rewrite add_comm.
        apply DN.weakening.
        rewrite union_sym.
        rewrite <- union_rec_right.
        apply DN.weakening_env.
        assumption.
      + rewrite add_comm.
        apply DN.weakening.
        rewrite <- union_rec_right.
        apply DN.weakening_env.
        assumption.
    - (* 13 *)
      rewrite union_rec_left in H0.
      eapply (disj_or) in H0.
      2:{ reflexivity. }
      (* rewrite <- union_rec_left in H0. *)
      rewrite <- union_rec_right in H0.
      rewrite <- union_rec_left in H0.
      apply (IHpf φ0 (ψ :: B')).
      assumption.
    - (* 14 *)
      rewrite union_rec_left in H0.
      eapply disj_or in H0.
      2:{ reflexivity. }
      rewrite add_comm in H0.
      rewrite <- union_rec_right in H0.
      rewrite <- union_rec_left in H0.
      apply (IHpf φ0 (φ::B')).
      assumption.
    - (* 15 *)
      assert (is_ms_disj (φ∨φ0) (φ::((Δ ∪ Δ') ∪ B'))).
      { econstructor 3;eauto;myauto. }
      rewrite <- union_assoc in H2.
      rewrite <- union_rec_left in H2.
      specialize IHpf1 with (1:=H2).
      setoid_rewrite union_sym at 2 in H1.
      rewrite <- union_assoc in H1.
      specialize IHpf2 with (1:= H1).
      (* On sait que A ⊢dn c ∨ φ. On peut donc utiliser la règle "ore"
         et prouver que
         - en supposant c ça marche car (c ∧ c⇒d) donne d et d::A' ⊢ φ
         - en supposant φ ça marche trivialement car φ ⊢ φ. *)
      apply DN.ore with (φ₁:=φ)(φ₂:=φ0).
      + apply DN.weakening.
        rewrite union_sym.
        now apply DN.weakening_env.
      + eapply DN.impe with (φ₁:=ψ).
        * apply DN.impi.
          rewrite add_comm.
          apply DN.weakening.
          rewrite add_comm.
          apply DN.weakening.
          rewrite union_sym.
          rewrite <- union_rec_left.
          rewrite union_sym.
          now apply DN.weakening_env.
        * eapply DN.impe with (φ₁:=φ).
          -- DN.tax.
          -- DN.tax.
      + DN.tax.
    - (* 16 *)
      assert (is_ms_disj (ψ ∨ φ0) (ψ :: Δ ∪ (φ ⇒ ψ) :: B')).
      { econstructor 3;eauto;myauto.
        rewrite union_rec_left.
        rewrite union_rec_right.
        setoid_rewrite union_rec_left at 2.
        reflexivity. }
      specialize IHpf with (1:=H1).
      apply rimp_ok in IHpf.
      rewrite union_rec_left in H0.
      addunionh H1.
      apply inversion_disj_union in H0.
      destruct H0 as [f [f' [hperm  [ hf hf'(* [ hψ' hΔ ] *) ] ] ] ].
      specialize is_ms_disj_singleton with (1:=hf)(φ':=φ⇒ψ)(2:=eq_refl _) as h.
      rewrite hperm,h in IHpf.
      rewrite Ou_assoc in IHpf.
      rewrite Ou_same in IHpf.
      rewrite hperm,h.
      assumption.
Qed.


Theorem trad_lk_dn:  forall A B φ, A ⊢ B -> is_ms_disj φ B -> A ⊢dn φ.
Proof.
  intros A B φ H H0. 
  apply trad_lk_dn_full with (B:=B) (B':=∅).
  - assumption.
  - rewrite union_empty_right.
    assumption.
Qed.
