From Stdlib Require Import Utf8_core Lia FunInd
  FMapInterface FMapFacts FMapWeakList
  FMapAVL DecidableType OrderedType.

Require Import multiset_spec MiscFacts.

Module PreMake(X:DecidableType)(Maps:FMapInterface.WS with Module E:=X) <: S(X).
  Module MapsFact := WFacts(Maps).


  Local Notation A := X.t.
  Definition t := Maps.t nat.

  Definition empty : t := Maps.empty nat.

  Definition is_empty : t  -> bool := @Maps.is_empty nat.

  Definition Empty: t → Prop := @Maps.Empty nat.

  Definition multiplicity: A -> t -> option nat := @Maps.find nat.

  Definition Multiplicity: A -> nat -> t -> Prop := @Maps.MapsTo nat.

  Definition add_multiple : A -> nat -> t -> t :=
    fun a n ms =>
      Maps.add a (match multiplicity a ms with 
                    | Some v => (S (plus n v))
                    | None => n
                  end) ms. 

  Definition Add_multiple x n m m' :=
    forall y, multiplicity y m' = multiplicity y (add_multiple x n m).


  Fixpoint iter (B:Type) (f:A -> B -> B) (k:A) (v:nat) (acc:B) {struct v} : B := 
    match v with 
      | 0 => f k acc
      | S n => f k (iter B f k n acc)
    end.
    
  Definition fold (B:Type) (f:A -> B -> B) ms v0 := 
    Maps.fold (iter B f) ms v0.

  Definition add : A -> t -> t := fun a ms => add_multiple a 0 ms.

  Definition Add x m m' :=
    forall y, multiplicity y m' = multiplicity y (add x m).

(*   Lemma add_add_multiple : forall a ms, add a ms = add_multiple a 0 ms. *)

  Lemma Multiplicity_multiplicity :
    forall a n ms,
      Multiplicity a n ms <-> multiplicity a ms = Some n.
  Proof.
    intros a n ms.
    unfold Multiplicity,multiplicity in *.
    apply MapsFact.find_mapsto_iff.
  Qed.

  Definition remove : A -> t -> t := 
    fun a ms => 
      match multiplicity a ms with 
        | Some 0 =>  Maps.remove a ms
        | Some (S v) =>  (Maps.add a v ms)
        | None => ms
      end.

  Definition remove_all : A -> t -> t := fun a ms => Maps.remove a ms.

  Definition mem : A -> t -> bool := @Maps.mem nat. 
  Definition In : A -> t -> Prop := @Maps.In nat. 

  Definition elements_mult: t -> List.list (A*nat) := @Maps.elements _.
  Definition elements (m:t): List.list A := List.map (@fst _ _) (@Maps.elements _ m).

  Definition eq_bool : t -> t -> bool := Maps.equal nat_eq_bool.

(*   Definition eq : t -> t -> Prop := @Maps.Equal nat.  *)

  Definition eq m m' : Prop :=
    forall y : Maps.key, multiplicity y m = multiplicity y m'.

  Lemma Add_multiple_add_multiple :
    forall a n ms ms', eq (add_multiple a n ms) (ms') <-> Add_multiple a n ms ms'.
  Proof.
    intros a n ms ms'.
    split.
    - intros haddm.
      red.
      intros y.
      rewrite haddm.
      reflexivity.
    - intros H.
      unfold Add_multiple in *.
      intros y.
      rewrite H.
      reflexivity.
  Qed.


  Lemma eq_Equal : forall x y, eq x y <-> Maps.Equal x y.
  Proof.
    intros x y.
    split;intro h.
    - rewrite h.
      reflexivity.
    - rewrite h.
      reflexivity.
  Qed.

  Definition eq_refl : forall ms, eq ms ms := @MapsFact.Equal_refl nat.

  Definition eq_sym : forall ms ms', eq ms ms' -> eq ms' ms := @MapsFact.Equal_sym nat.

  Definition eq_trans : forall ms1 ms2 ms3, eq ms1 ms2 -> eq ms2 ms3 -> eq ms1 ms3 := @MapsFact.Equal_trans nat.


  Definition union : t -> t -> t := fun ms1 ms2 => 
    Maps.fold add_multiple ms1 ms2.

  Module MapsPtes := FMapFacts.Properties(Maps).

  Add Morphism add_multiple with signature X.eq ==> (@Logic.eq nat) ==> eq ==> eq as add_multiple_morph.
  Proof.
    intros x y H y0 x0 y1 H0.
    unfold add_multiple.
    rewrite H.
    rewrite H0.
    reflexivity.
  Qed.

  Add Morphism multiplicity with signature X.eq ==> eq ==> (@Logic.eq (option nat)) as multiplicity_morph.
  Proof.
    intros x y heqxy x0 y0 heqms.
    unfold add_multiple.
    rewrite heqxy.
    rewrite heqms.
    reflexivity.
  Qed.

  Add Morphism Multiplicity with signature X.eq ==> @Logic.eq nat ==> eq ==> iff as Multiplicity_morph.
  Proof.
    intros x y heqxy x0 y0 z0 heqms.
    unfold Multiplicity.
    rewrite heqms,heqxy.
    reflexivity.
  Qed.


  Lemma Add_multiple_meq:
    forall m m' k v,
      Add_multiple k v m m'
      <-> eq m' (add_multiple k v m).
  Proof.
    unfold eq, Add_multiple in *.
    intros m m' k v.
    split; intros y;eauto.
  Qed.


  Lemma add_spec_mult:
    forall a m n,
      multiplicity a m = Some n
      -> multiplicity a (add a m) = Some (S n).
  Proof.
    intros a m n H.
    unfold add,add_multiple.
    rewrite H.
    apply MapsFact.add_eq_o.
    reflexivity.
  Qed.

  Lemma add_spec_Mult:
    forall a m n,
      Multiplicity a n m
      -> Multiplicity a  (S n) (add a m).
  Proof.
    intros a m n H.
    unfold Multiplicity, add,add_multiple, multiplicity in *.
    rewrite MapsFact.find_mapsto_iff in H.
    rewrite H.
    apply Maps.add_1.
    reflexivity.
  Qed.

  Lemma in_addm_eq : forall a b n m,
                      X.eq a b ->
                      In a (add_multiple b n m).
  Proof.
    intros a b n m H.
    unfold In,add_multiple.
    rewrite MapsFact.add_in_iff.
    left.
    symmetry.
    assumption.
  Qed.

  Lemma in_add_eq : forall a b m,
                      X.eq a b ->
                      In a (add b m).
  Proof.
    intros a b m H.
    apply in_addm_eq.
    assumption.
  Qed.



  Lemma add_spec_zero:
    forall a m,
      multiplicity a m = None
      -> multiplicity a (add a m) = Some O.
  Proof.
    intros a m H.
    unfold add,add_multiple.
    rewrite H.
    apply MapsFact.add_eq_o.
    reflexivity.
  Qed.

  Lemma add_spec_zero_Mult:
    forall a m,
      ~In a m
      -> Multiplicity a 0 (add a m).
  Proof.
    intros a m H.
    unfold add,add_multiple.
    rewrite Multiplicity_multiplicity.
    unfold In,multiplicity in *.
    apply MapsFact.not_find_in_iff in H.
    rewrite H.
    apply MapsFact.add_eq_o.
    reflexivity.
  Qed.

  Lemma mem_in_iff: forall m x, In x m <-> mem x m = true.
  Proof.
    exact (@MapsFact.mem_in_iff nat).
  Qed.

  Lemma not_mem_in_iff: forall m x, ~In x m <-> mem x m = false.
  Proof.
    exact (@MapsFact.not_mem_in_iff nat).
  Qed.

  Lemma in_find_iff: forall m x, In x m <-> multiplicity x m <> None.
  Proof.
    exact (@MapsFact.in_find_iff nat).
  Qed.

  Lemma not_find_in_iff: forall m x, ~In x m <-> multiplicity x m = None.
  Proof.
    exact (@MapsFact.not_find_in_iff nat).
  Qed.


  Lemma add_multiple_neq_o:
    ∀ m x y e,
      ¬X.eq x y → multiplicity y (add_multiple x e m) = multiplicity y m.
  Proof.
    unfold multiplicity,add_multiple.
    intros m x y e H.
    destruct (multiplicity x m).
    - rewrite MapsPtes.F.add_neq_o;auto.
    - rewrite MapsPtes.F.add_neq_o;auto.
  Qed.

  Lemma add_multiple_eq_o:
    ∀ m x y e,
      multiplicity y m = None
      -> X.eq x y
      -> multiplicity y (add_multiple x e m) = Some e.
  Proof.
    intros m x y e H H0.
    unfold add_multiple.
    rewrite H0.
    rewrite H.
    unfold multiplicity.
    rewrite MapsPtes.F.add_eq_o;auto.
  Qed.

  Lemma add_multiple_eq_o_2:
    ∀ m x y e' e res,
      multiplicity y m = Some e'
      -> X.eq x y
      -> res = S(e+e')
      -> multiplicity y (add_multiple x e m) = Some res.
  Proof.
    intros m x y e' e res H H0.
    unfold add_multiple.
    rewrite H0.
    rewrite H.
    unfold multiplicity.
    rewrite MapsPtes.F.add_eq_o;auto.
  Qed.

  Lemma add_neq_o:
    ∀ m x y,
      ¬X.eq x y → multiplicity y (add x m) = multiplicity y m.
  Proof.
    intros m x y H.
    apply add_multiple_neq_o.
    assumption.
  Qed.


  Lemma add_eq_o_2:
    ∀ m x y e',
      multiplicity y m = Some e'
      -> X.eq x y
      -> multiplicity y (add x m) = Some (S e').
  Proof.
    intros m x y e' H H0.
    eapply add_multiple_eq_o_2;eauto.
  Qed.

  Lemma add_eq_o:
    ∀ m x y,
      multiplicity y m = None
      -> X.eq x y
      -> multiplicity y (add x m) = Some 0.
  Proof.
    intros m x y H H0.
    eapply add_multiple_eq_o;eauto.
  Qed.

  Lemma in_addm_neq: forall f f' n m, ~ X.eq f' f -> (In f (add_multiple f' n m) <-> In f m).
  Proof.
    intros f f' n m h.
    setoid_rewrite in_find_iff at 2.
    rewrite <- (add_multiple_neq_o _ f' f n).
    - setoid_rewrite in_find_iff.
      reflexivity.
    - assumption.
  Qed.

  Lemma in_addm: forall f f' n m, In f m -> In f (add_multiple f' n m).
  Proof.
    intros f f' n m h.
    setoid_rewrite in_find_iff in h.
    apply in_find_iff.
    apply MiscFacts.not_None_destruct in h.
    apply MiscFacts.not_None_destruct.
    destruct h.
    destruct (X.eq_dec f f').
    - exists (S(n+x)).
      eapply (add_multiple_eq_o_2 _ f' f x n);auto.
    - exists x.
      rewrite add_multiple_neq_o;auto.
  Qed.

  Lemma in_add_neq: forall f f' m, ~ X.eq f' f -> (In f (add f' m) <-> In f m).
  Proof.
    unfold add.
    intros f f' m.
    apply in_addm_neq.
  Qed.

  Lemma in_add: forall f f' m, In f m -> In f (add f' m).
  Proof.
    intros f f' m H.
    unfold add.
    apply in_addm.
    assumption.
  Qed.

  
  Lemma add_morph_eq : forall a a', X.eq a a' -> forall ms ms',  eq ms ms' -> eq (add a ms) (add a' ms'). 
  Proof.
    intros a a' H ms ms' H0.
    unfold eq in *.
    intros y.
    destruct (X.eq_dec y a'). 
    - destruct (multiplicity y ms) eqn: heq.
      + setoid_rewrite (add_eq_o_2 _ _ _ n);eauto.
        rewrite <- H0.
        assumption.
      + setoid_rewrite add_eq_o;eauto.
        rewrite <- H0.
        assumption.
    - setoid_rewrite add_neq_o;eauto.
Qed.


  Lemma add_comm_aux : 
    forall (B : Type)
      (k : A)
      (k' : A)
      (v : B)
      (v' : B)
      (m : Maps.t B)
      (H : ~ X.eq k k')
      (alpha : Maps.key)
      (e : B),
      Maps.MapsTo alpha e (Maps.add k v (Maps.add k' v' m)) ->
      Maps.MapsTo alpha e (Maps.add k' v' (Maps.add k v m)).
  Proof.
    intros B k k' v v' m H alpha e H0.
    case_eq (X.eq_dec alpha k);intros alpha_eq_k _.
    rewrite alpha_eq_k in H0|-*.
    clear alpha_eq_k.
    assert(H1:Maps.MapsTo k v (Maps.add k v (Maps.add k' v' m))).
    apply Maps.add_1.
    reflexivity.
    assert (h1:=MapsPtes.F.MapsTo_fun H0 H1).
    subst.
    apply Maps.add_2.
    intros abs. 
    symmetry in abs.
    elim H.
    rewrite abs.
    reflexivity. 
    apply Maps.add_1.
    reflexivity.
    case_eq (X.eq_dec alpha k');intros alpha_eq_k' _.
    rewrite alpha_eq_k' in H0|-*.
    clear alpha_eq_k'.
    apply Maps.add_3 in H0;[ | assumption].
    assert(H1:Maps.MapsTo k' v' (Maps.add k' v' m)).
    apply Maps.add_1.
    reflexivity.
    assert (h1:=MapsPtes.F.MapsTo_fun H0 H1).
    subst.
    apply Maps.add_1.
    reflexivity. 
    apply Maps.add_2.
    intros abs. 
    symmetry in abs.
    elim alpha_eq_k'.
    assumption.
    apply Maps.add_2.
    intros abs. 
    symmetry in abs.
    elim alpha_eq_k.
    assumption.
    apply Maps.add_3 in H0.
    apply Maps.add_3 in H0.
    assumption.
    intros abs. 
    symmetry in abs.
    elim alpha_eq_k'.
    assumption.
    intros abs. 
    symmetry in abs.
    elim alpha_eq_k.
    assumption.
  Qed.


  (* Lemma on maps *)
  Lemma mapadd_comm' : forall B k k' (v v':B) m , 
    ~ X.eq k k' ->
    Maps.Equal (Maps.add k v (Maps.add k' v' m))
     (Maps.add k' v' (Maps.add k v m)).
  Proof.
    intros B k k' v v' m H.
    rewrite MapsPtes.F.Equal_mapsto_iff.
    intros alpha e.
    split;intros H1.
    apply add_comm_aux;assumption.
    apply add_comm_aux;try assumption.
    intros abs. 
    symmetry in abs.
    elim H.
    assumption.
  Qed.


  Lemma add_comm' : forall k k' v v' m , 
    ~ X.eq k k' ->
    eq (add_multiple k v (add_multiple k' v' m))
     (add_multiple k' v' (add_multiple k v m)).
  Proof.
    intros k k' v v' m H.
    unfold eq,add_multiple.
    intros y.
    destruct (multiplicity k' m) eqn:heq; destruct (multiplicity k m) eqn:heq'
    ; unfold multiplicity in *;
    setoid_rewrite MapsPtes.F.add_neq_o at 2 4;auto;
    rewrite heq',heq; apply mapadd_comm';auto.
  Qed.



  Lemma Addm_In_other : forall n k k' m m',
                    In k m -> Add_multiple k' n m m' -> In k m'.
  Proof.
    intros n k k' m m' H H0.
    red.
    red in H,H0.
    unfold add_multiple,multiplicity in H0.
    rewrite MapsFact.in_find_iff in *.
    intro abs.
    specialize (H0 k).
    rewrite H0 in abs.
    clear H0.
    destruct (Maps.find k' m).
    - destruct (X.eq_dec k k') as [heq|heq].
      + rewrite heq in abs.
        rewrite MapsFact.add_eq_o in abs.
        * inversion abs.
        * reflexivity.
      + rewrite MapsFact.add_neq_o in abs.
        * contradiction.
        * intro abs'.
          rewrite abs' in heq.
          apply heq.
          reflexivity.
    - destruct (X.eq_dec k k') as [heq | heq].
      + rewrite heq in abs.
        rewrite MapsFact.add_eq_o in abs.
        * inversion abs.
        * reflexivity.
      + rewrite MapsFact.add_neq_o in abs.
        * contradiction.
        * intro abs'.
          rewrite abs' in heq.
          apply heq.
          reflexivity.
  Qed.

  Lemma Add_Add_multiple : forall m m' k, Add k m m' <-> Add_multiple k 0 m m'.
  Proof.
    intros m m' k.
    unfold Add,Add_multiple.
    unfold add.
    reflexivity.
  Qed.

  Lemma Add_In_other : forall k k' m m',
                    In k m -> Add k' m m' -> In k m'.
  Proof.
    intros k k' m m' H H0.
    rewrite Add_Add_multiple in H0.
    eapply Addm_In_other;eauto.
  Qed.

  Lemma Add_multiple_of_add_multiple :
    forall x n Γ,
      Add_multiple x n Γ (add_multiple x n Γ).
  Proof.
    intros x n Γ.
    hnf.
    intros y.
    reflexivity.
  Qed.        

  Lemma Add_of_add :
    forall x Γ, Add x Γ (add x Γ).
  Proof.
    intros x n Γ.
    reflexivity.
  Qed.


  Lemma Addm_multiplicity:
    forall φ n Γ Γ',
      Add_multiple φ n Γ Γ' ->
      exists m, Multiplicity φ m Γ'.
  Proof.
    intros φ n Γ Γ' H.
    unfold Add_multiple,add_multiple in H.
    destruct ( multiplicity φ Γ).
    - exists (S (n + n0)).
      apply Multiplicity_multiplicity.
      rewrite H.
      apply MapsFact.add_eq_o.
      reflexivity.
    - exists n.
      apply Multiplicity_multiplicity.
      rewrite H.
      apply MapsFact.add_eq_o.
      reflexivity.
  Qed.

  Lemma Addm_In : forall φ n Γ Γ',
                    Add_multiple φ n Γ Γ'
                    -> In φ Γ'.
  Proof.
    intros φ n Γ Γ' H0.
    destruct (Addm_multiplicity _ _ _ _ H0).
    red.
    unfold Multiplicity in *.
    apply MapsFact.in_find_iff.
    apply MapsFact.find_mapsto_iff in H.
    rewrite H.
    intro abs; inversion abs.
  Qed.


  Lemma transpose_neqkey_equal_add_multiple : MapsPtes.transpose_neqkey eq add_multiple.
  Proof.
    red.
    intros k k' e e' a H.
    apply add_comm'.
    assumption;
    case_eq (multiplicity k' a);case_eq (multiplicity k a).
  Qed.

  Lemma empty_o: forall x, multiplicity x empty = None.
  Proof.
    intros x.
    unfold multiplicity,empty.
    apply MapsFact.empty_o.
  Qed.

  Lemma union_morph_eq : forall a a', eq a a' -> forall ms ms',  eq ms ms' -> eq (union a ms) (union a' ms'). 
  Proof. (* fold_rec *)
    intros a a' H ms ms' H0.
    revert a' H ms' H0.
    unfold union,multiplicity in *.
    pattern a,(Maps.fold add_multiple a ms).
    apply MapsPtes.fold_rec_bis.

    { intros m m' a0 H H0 a' H1 ms' H2.
      apply H0.
      setoid_rewrite H;exact H1.
      assumption. }

    { intros a' H ms' H0 y.
      rewrite MapsPtes.fold_Empty;auto.
      clear -H.
      red. intros a e. intro abs.
      specialize(H a).
      rewrite empty_o in H.
      rewrite MapsPtes.F.find_mapsto_iff in abs.
      setoid_rewrite abs in H.
      inversion H. }

    { intros k e a0 m' H H0 H1 a' H2 ms' H3 y.
      rewrite <- MapsPtes.fold_Equal.
      5:eexact H2.
      - rewrite MapsPtes.fold_add.
        + rewrite H1.
          reflexivity.
          reflexivity.
          assumption.
        + auto with *.
        + apply add_multiple_morph_Proper.
        + apply transpose_neqkey_equal_add_multiple.
        + assumption.
      - auto with *.
      - apply add_multiple_morph_Proper.
      - apply transpose_neqkey_equal_add_multiple. }
  Qed.

  Lemma is_empty_empty : is_empty empty = true.
  Proof.
    unfold is_empty,empty.
    rewrite <- MapsPtes.F.is_empty_iff.
    apply Maps.empty_1.
  Qed.  

  Lemma Empty_empty : Empty empty.
  Proof.
    apply Maps.empty_1.
  Qed.

  Lemma is_empty_Empty : forall ms, Empty ms <-> is_empty ms = true.
  Proof.
    intros ms.
    unfold Empty,is_empty.
    apply MapsFact.is_empty_iff.
  Qed.

  Lemma Empty_no_mem : forall ms, Empty ms <-> (forall a, ~In a ms). 
  Proof.
    intros ms.
    unfold In,Empty,Maps.Empty,Maps.In.
    split;intros.
    - intro abs.
      destruct abs.
      destruct (H _ _ H0).
    - intro abs.
      destruct (H a).
      exists e;assumption.
  Qed.

  Lemma in_empty_false : forall Γ, Empty Γ -> forall f, In f Γ <-> False.
  Proof.
    intros Γ H f.
    split;try contradiction.
    intros abs.
    assert (~In f Γ).
    { apply Empty_no_mem. assumption. }
    contradiction.
  Qed.

  Lemma is_empty_no_mem : forall ms, is_empty ms = true <-> (forall a, mem a ms = false). 
  Proof.
    intros ms.
    unfold is_empty,mem.
    rewrite <- MapsPtes.F.is_empty_iff.
    unfold Maps.Empty.
    split;intros H a.
    rewrite MapsFact.mem_find_b. 
    case_eq (Maps.find a ms).
    intros n abs;elim (H a n).
    rewrite (MapsPtes.F.find_mapsto_iff);assumption.
    reflexivity.
    intros v abs.
    rewrite (MapsPtes.F.find_mapsto_iff) in abs.
    assert (H1:=H a).
    generalize (MapsFact.mem_find_b ms a). 
    rewrite abs.
    rewrite H1;discriminate.
  Qed.




  Lemma add_is_not_empty : forall a ms, is_empty (add a ms) = false.
  Proof.
    unfold is_empty, add,add_multiple,multiplicity.
    intros a ms.
    destruct (Maps.find a ms).
    - assert (H:~ (Maps.Empty (Maps.add a (S n) ms))).
      + intros abs;unfold Maps.Empty in abs.
        apply (abs a (S n)).
        rewrite MapsPtes.F.add_mapsto_iff.
        left;auto.
      + rewrite MapsPtes.F.is_empty_iff in H.
        destruct (Maps.is_empty (Maps.add a (S n) ms)).
        * elim H;reflexivity.
        * simpl.
          destruct (Maps.is_empty (Maps.add a (S n) ms)) eqn:hhh;auto.
          apply Maps.is_empty_2 in hhh.
          unfold Maps.Empty in hhh.
          specialize (hhh a (S n)).
          destruct hhh.
          apply Maps.add_1.
          reflexivity.
    - assert (H:~ (Maps.Empty (Maps.add a 0 ms))).
      intros abs;unfold Maps.Empty in abs.
      apply (abs a 0).
      rewrite MapsPtes.F.add_mapsto_iff.
      left;auto.
      rewrite MapsPtes.F.is_empty_iff in H.
      destruct (Maps.is_empty (Maps.add a 0 ms)).
      elim H;reflexivity.
      reflexivity.
  Qed.

  Lemma add_is_mem : forall a b ms, X.eq a b -> mem a (add b ms) = true.
  Proof.
    unfold mem,add,add_multiple,multiplicity.
    intros a b ms Heq.
    destruct (Maps.find b ms);  apply MapsPtes.F.add_eq_b;symmetry;assumption. 
  Qed.

  Lemma mem_destruct : forall a b ms, mem a (add b ms) = true -> X.eq a b \/ mem a ms = true.
  Proof.
    intros a b ms.
    case (X.eq_dec a b).
    auto.
    unfold mem,add,add_multiple,multiplicity.
    intros neq.    
    destruct (Maps.find b ms); rewrite MapsPtes.F.add_neq_b;auto.
  Qed.
  
  Lemma mem_add_is_mem : forall a b ms, mem a ms = true -> mem a (add b ms) = true.
  Proof.
    intros a b ms.
    case (X.eq_dec a b).
    intros e H.
    apply add_is_mem;assumption.
    unfold mem,add,add_multiple,multiplicity.
    intros n H.
    destruct (Maps.find b ms); rewrite MapsPtes.F.add_neq_b;auto.    
  Qed.

  Lemma mem_destruct_iff : forall a b ms, mem a (add b ms) = true <-> X.eq a b \/ mem a ms = true.
  Proof.
    intros a b ms.
    split;intro.
    - apply mem_destruct;assumption.
    - destruct H.
      + apply add_is_mem;assumption.
      + apply mem_add_is_mem;assumption.
  Qed.

  Lemma In_destruct_iff : forall a b ms, In a (add b ms) <-> X.eq a b \/ In a ms.
  Proof.
    intros a b ms.
    setoid_rewrite mem_in_iff.
    apply mem_destruct_iff.
  Qed.

  Lemma add_add_eq: forall A x (v v':A) ms,
                      Maps.Equal (Maps.add x v (Maps.add x v' ms))
                                 (Maps.add x v ms).
  Proof.
    intros A x v v' ms.
    unfold Maps.Equal.
    intros y.
    destruct  (X.eq_dec y x);intros.
    - setoid_rewrite MapsFact.add_eq_o;auto.
    - setoid_rewrite MapsFact.add_neq_o;auto.
      setoid_rewrite MapsFact.add_neq_o;auto.
  Qed.

  Lemma neq_sym: forall x x', ¬X.eq x' x -> ¬X.eq x x'.
  Proof.
    intros x x' H.
    intro abs.
    symmetry in abs.
    elim (H abs).
  Qed.

  Lemma add_add_neq: forall A x y (v v':A) ms,
                       ~X.eq x y ->
                       Maps.Equal (Maps.add x v (Maps.add y v' ms))
                                  (Maps.add y v' (Maps.add x v ms)).
  Proof.
    intros A x x' v v' ms hneq.
    unfold Maps.Equal.
    intros y.
    destruct  (X.eq_dec y x);intros.
    - setoid_rewrite MapsFact.add_eq_o at 1;auto.
      setoid_rewrite MapsFact.add_neq_o;auto.
      + symmetry. apply MapsFact.add_eq_o. auto.
      + rewrite e.
        apply neq_sym.
        assumption.
    - destruct  (X.eq_dec y x');intros.
      + setoid_rewrite MapsFact.add_eq_o at 2;auto.
        setoid_rewrite MapsFact.add_neq_o;auto.
        rewrite e.
        apply MapsFact.add_eq_o. auto.
      + setoid_rewrite MapsFact.add_neq_o;auto.
        setoid_rewrite MapsFact.add_neq_o;auto.
  Qed.


  Lemma add_multiple_comm : 
    forall a v1 b v2 ms, 
      eq 
        (add_multiple a v1 (add_multiple b v2 ms)) 
        (add_multiple b v2 (add_multiple a v1 ms)).
  Proof.
    unfold eq,add_multiple,multiplicity.
    intros a v1 b v2 ms.
    case (X.eq_dec a b);intros a_eq_b y.
    rewrite a_eq_b.

    { case_eq (Maps.find b ms);[intro n1 |];intro Heq1.
      - setoid_rewrite MapsPtes.F.add_eq_o at 2 4; try reflexivity.
        setoid_rewrite add_add_eq.
        apply f_equal2;auto.
        apply f_equal2;auto.
        lia.
      - setoid_rewrite MapsPtes.F.add_eq_o at 2 4; try reflexivity.
        setoid_rewrite add_add_eq.
        apply f_equal2;auto.
        apply f_equal2;auto.
        lia. }

    { case_eq (Maps.find b ms);[intro n1 |];intro Heq1.
      - setoid_rewrite MapsPtes.F.add_neq_o at 2 4; auto.
        rewrite Heq1.
        setoid_rewrite add_add_neq;auto.
        case_eq (Maps.find a ms);[intro n2 |];intro Heq2;auto.
        + setoid_rewrite add_add_neq at 1;auto.
        + setoid_rewrite add_add_neq at 1;auto.
      - setoid_rewrite MapsPtes.F.add_neq_o at 2 4; auto.
        setoid_rewrite add_add_neq;auto.
        rewrite Heq1.
        setoid_rewrite add_add_neq at 1;auto. }
  Qed.

  Lemma add_comm : forall a b ms, eq (add a (add b ms)) (add b (add a ms)).
  Proof.
    intros a b ms.
    apply add_multiple_comm.
  Qed.

  (*  Lemma mem_add_comm : forall a b ms, mem a ms = true -> mem a (add b ms) = true.
  Proof.
    exact mem_add_is_mem.
  Qed.
   *)
  Lemma union_empty_left : forall ms, eq (union empty ms) ms.
  Proof.
    intros ms.
    unfold union,empty,multiplicity.
    apply MapsPtes.fold_Empty.
    auto with *.
    apply Maps.empty_1.
  Qed.

  Lemma fold_pseudo_morph : 
    forall 
      (f : Maps.key -> nat -> t -> t)
      (f_morph: 
         forall k k' n ms ms', 
           X.eq k k' ->
           eq ms ms' -> 
           eq (f k n ms) (f k n ms'))
      (f_proper : (Proper (X.eq ==> Logic.eq ==> eq ==> eq) f))
      (f_transpose:MapsPtes.transpose_neqkey Maps.Equal f )
      (* (f_in : forall k e a, Maps.find k (f k e a) = Some e) *)
      (f_in' : forall k e a k', ~X.eq k k' -> Maps.find k' (f k e a) = Maps.find k' a)
      (ms1 : Maps.t nat)
      (ms1' : Maps.t nat)
      (H1 : eq ms1 ms1')
      (ms2 : Maps.t nat)
      (ms2' : Maps.t nat)
      (H2 : eq ms2 ms2'),
      eq (Maps.fold f ms1 ms2) (Maps.fold f ms1' ms2').
  Proof.
    intros f f_morph f_proper f_transpose (* f_in *) f_in' ms1 ms1' H1 ms2 ms2' H2.
    revert ms1' H1 ms2' H2.
    pattern ms1,(Maps.fold f ms1 ms2).
    apply MapsPtes.fold_rec.

    { intros m H ms1' H1 ms2' H2.
      rewrite MapsPtes.fold_Empty.
      - assumption.    
      - auto with *.
      - rewrite <- H1.
        assumption. }

    { intros k e a m' m'' H H0 H1 H2 ms1' H3 ms2' H4.
      intros k'.
      case (X.eq_dec k k');intros k_eq_k'.
      - rewrite <- k_eq_k' in *.
        assert (Equivalence (@Maps.Equal nat)).
        auto with *.
        rewrite (@MapsPtes.fold_Add nat _ (@Maps.Equal nat) H5 f f_proper f_transpose  m' ms1' k e);trivial .
        + apply (f_morph k k' e a (Maps.fold f m' ms2'));trivial.
          apply H2;trivial.
          reflexivity.
        + intro k''. 
          rewrite <- H3.
          apply H1.    
      - rewrite f_in'.
        + assert(MapsPtes.Add k e m' ms1').
          { intro k''. 
            rewrite <- H3.
            apply H1. }
          { rewrite MapsPtes.fold_Add.
            - rewrite f_in'.
              + apply H2.
                reflexivity.
                assumption.
              + eassumption.
            - auto with *.
            - assumption.
            - assumption.
            - assumption.
            - eexact H5. }
        + assumption. }
  Qed.

  Lemma empty_no_mem : forall a, mem a empty = false.
  Proof.
    unfold mem.
    apply MapsPtes.F.empty_a.
  Qed.

  Lemma union_empty_right : forall ms, eq (union ms empty) ms.
  Proof.
    intros ms.
    unfold union,empty,multiplicity.
    rewrite eq_Equal.

    assert (morph:
              forall (ms1 : Maps.t nat)
                     (ms1' : Maps.t nat)
                     (H1 : eq ms1 ms1')
                     (ms2 : Maps.t nat)
                     (ms2' : Maps.t nat)
                     (H2 : eq ms2 ms2'),
                eq (Maps.fold add_multiple ms1 ms2) (Maps.fold add_multiple ms1' ms2')).
    { apply fold_pseudo_morph.
      - intros k k' n ms0 ms'0 H H0.
        apply add_multiple_morph;trivial.
      - apply add_multiple_morph_Proper.
      - apply transpose_neqkey_equal_add_multiple.
      - intros k e a k' H.
        unfold add_multiple,multiplicity.
        destruct (Maps.find k a).
        + apply MapsPtes.F.add_neq_o;trivial.
        + apply MapsPtes.F.add_neq_o;trivial. }
    pattern ms,(Maps.fold add_multiple ms (Maps.empty nat)).
    apply MapsPtes.fold_rec_bis.
    - intros m m' a heq heq'.
      transitivity m;assumption.
    - reflexivity.
    - intros k e a m' H H0 H1.
      unfold add_multiple,multiplicity.
      case_eq (Maps.find k a);[intros n|];intro Heq.
      + rewrite MapsPtes.F.not_find_in_iff in H0.
        rewrite H1 in Heq.
        rewrite Heq in H0;discriminate.
      + rewrite H1;reflexivity.
  Qed.

  (* Lemma on Maps. *)
  Lemma Empty_not_find : 
    forall elt a (m:Maps.t elt), 
      Maps.Empty m -> Maps.find a m = (@None elt).
  Proof.
    intros elt a m H.
    red in H.
    case_eq (Maps.find a m);[intro e|];intro Heq.
    elim (H a e).
    rewrite MapsPtes.F.find_mapsto_iff;assumption.
    reflexivity.
  Qed.

  Lemma empty_unique :
    forall Γ Γ': t,
      Empty Γ ->
      Empty Γ' ->
      eq Γ Γ'.
  Proof.
    intros Γ Γ' H H0.
    unfold eq.
    intros y.
    unfold multiplicity.
    rewrite Empty_not_find.
    - rewrite Empty_not_find.
      + reflexivity.
      + assumption.
    - assumption.
  Qed.

  Lemma add_multiple_multiple : forall a v1 v2 m, 
                                  eq (add_multiple a v1 (add_multiple a v2 m)) (add_multiple a (S (v1+v2)) m).
  Proof.
    setoid_rewrite eq_Equal.
    intros a v1 v2 m.
    unfold add_multiple,multiplicity.
    case_eq (Maps.find a m);[intro n| ];intro Heq1.
    rewrite MapsPtes.F.add_eq_o;[|reflexivity].
    intros k.
    case(X.eq_dec k a);intro Heq2.
    rewrite MapsPtes.F.add_eq_o;[|symmetry;assumption].
    rewrite MapsPtes.F.add_eq_o;[|symmetry;assumption].
    f_equal;lia.
    do 3 (rewrite MapsPtes.F.add_neq_o;[|intros abs;elim Heq2;rewrite abs;reflexivity]).
    reflexivity.
    rewrite MapsPtes.F.add_eq_o;[|reflexivity].
    intro k.
    case(X.eq_dec k a);intro Heq2.
    rewrite MapsPtes.F.add_eq_o;[|symmetry;assumption].
    rewrite MapsPtes.F.add_eq_o;[|symmetry;assumption].
    reflexivity.
    do 3 (rewrite MapsPtes.F.add_neq_o;[|intros abs;elim Heq2;rewrite abs;reflexivity]).
    reflexivity.
  Qed.

  (* Lemma on Maps *)    
  Lemma add_add_add: 
    forall k k' v v' (m:t), 
      X.eq k k' ->
      Maps.Equal (Maps.add k v (Maps.add k' v' m)) (Maps.add k v m).
  Proof.
    intros k k' v v' m H.
    intros k''.
    rewrite H;clear H.
    case (X.eq_dec k' k'');intro Heq.
    do 2  (rewrite MapsPtes.F.add_eq_o;[|rewrite Heq;reflexivity]);reflexivity.
    do 3 (rewrite MapsPtes.F.add_neq_o;[|intro abs;elim Heq;rewrite abs;reflexivity]);reflexivity.
  Qed.

  Lemma addm_rec_left :
    forall (m1 m2: Maps.t nat) (k : Maps.key) (e : nat),
      eq (Maps.fold add_multiple (add_multiple k e m1) m2)
         (add_multiple k e (Maps.fold add_multiple m1 m2)).
  Proof.
    intros m1 m2.
    setoid_rewrite eq_Equal.
    assert (morph:
              forall (ms1 : Maps.t nat)
                     (ms1' : Maps.t nat)
                     (H1 : Maps.Equal ms1 ms1')
                     (ms2 : Maps.t nat)
                     (ms2' : Maps.t nat)
                     (H2 : Maps.Equal ms2 ms2'),
                Maps.Equal (Maps.fold add_multiple ms1 ms2) (Maps.fold add_multiple ms1' ms2')).
    { clear.
      apply fold_pseudo_morph.
      intros k k' n ms0 ms'0 H H0.
      apply add_multiple_morph;trivial.
      apply add_multiple_morph_Proper.
      apply transpose_neqkey_equal_add_multiple.
      intros k e a k' H.
      unfold add_multiple,multiplicity.
      destruct (Maps.find k a).
      apply MapsPtes.F.add_neq_o;trivial.
      apply MapsPtes.F.add_neq_o;trivial. }
    
    pattern m1,(Maps.fold add_multiple m1 m2).
    apply MapsPtes.fold_rec.

    { intros m H k e.
      unfold add_multiple at 2,multiplicity.
      replace (Maps.find k m) with (@None nat) by (symmetry;apply Empty_not_find;assumption).
      rewrite MapsPtes.fold_Add with (m1:=m) (k:=k) (e:=e);auto with *.
      rewrite MapsPtes.fold_Empty;auto with *.
      apply transpose_neqkey_equal_add_multiple.
      intros abs.
      red in abs.
      destruct abs as [v H1];elim (H k v H1).
      red;tauto. }

    { intros k e a m' m'' H H0 H1 H2 k0 e0.
      rewrite morph with (ms1':= (add_multiple k0 e0 (add_multiple k e m')))
                           (ms2':=m2);trivial; try reflexivity.
      - case (X.eq_dec k k0);intro Heq.
        + unfold add_multiple at 2 3 4 5, multiplicity.
          case_eq (Maps.find k a);[intro n|];intro Heq1.
          * rewrite <- Heq at 2 3 4.
            rewrite (MapsPtes.F.not_find_in_iff m' k) in H0.
            rewrite H0.
            do 2 (rewrite MapsPtes.F.add_eq_o;[|reflexivity]).
            rewrite morph with (ms1':=(add_multiple k0 (S (e0 + e)) m')) (ms2':=m2);trivial;try reflexivity. 
            rewrite (H2 k0 (S (e0+e))). 
            rewrite Heq.
            rewrite add_add_add.
            unfold add_multiple,multiplicity.
            rewrite Heq in Heq1;rewrite Heq1.
            replace ((S(e0 + e) + n)) with (e0 + (S (e + n))) by lia.
            reflexivity.
            reflexivity.
            rewrite add_add_add.
            unfold add_multiple,multiplicity.
            rewrite  Heq in H0.
            rewrite H0.
            reflexivity.
            rewrite <- Heq;reflexivity.
          * rewrite <- Heq at 2 3 4.
            rewrite (MapsPtes.F.not_find_in_iff m' k) in H0.
            rewrite H0.
            do 2 (rewrite MapsPtes.F.add_eq_o;[|reflexivity]).
            rewrite morph with (ms1':=(add_multiple k0 (S(e0 + e)) m')) (ms2':=m2);trivial;try reflexivity. 
            rewrite (H2 k0 (S(e0+e))). 
            rewrite Heq.
            rewrite add_add_add.
            unfold add_multiple,multiplicity.
            rewrite Heq in Heq1;rewrite Heq1.
            reflexivity.
            reflexivity.
            rewrite add_add_add.
            unfold add_multiple,multiplicity.
            rewrite  Heq in H0.
            rewrite H0.
            reflexivity.
            rewrite <- Heq;reflexivity.
        + rewrite morph with (ms1':= (add_multiple k e (add_multiple k0 e0 m')))
                               (ms2':=m2);trivial;try reflexivity.    
          * { rewrite MapsPtes.fold_Add with (k:=k) (e:=e) (m1:=(add_multiple k0 e0 m'));auto with *.
              - rewrite H2.
                rewrite add_multiple_comm;reflexivity.
              - apply transpose_neqkey_equal_add_multiple.
              - unfold add_multiple,multiplicity.
                destruct (Maps.find k0 m').
                + rewrite MapsPtes.F.add_in_iff.
                  intros abs;destruct abs.
                  * apply Heq;rewrite H3;reflexivity.
                  * apply H0;apply H3.
                + rewrite MapsPtes.F.add_in_iff.
                  intros abs;destruct abs.
                  * apply Heq;rewrite H3;reflexivity.
                  * apply H0;apply H3.
              - red.
                intro y.
                replace  (Maps.add k e (add_multiple k0 e0 m')) with 
                (add_multiple k e (add_multiple k0 e0 m')).
                { rewrite add_multiple_comm;reflexivity. }
                unfold  add_multiple at 1,multiplicity.
                assert (~Maps.In k (add_multiple k0 e0 m')).
                + unfold add_multiple,multiplicity.
                  destruct (Maps.find k0 m').
                  * rewrite MapsPtes.F.add_in_iff.
                    intros abs;destruct abs.
                    { apply Heq;rewrite H3;reflexivity. }
                    { apply H0;apply H3. }
                  * rewrite MapsPtes.F.add_in_iff.
                    intros abs;destruct abs.
                    { apply Heq;rewrite H3;reflexivity. }
                    { apply H0;apply H3. }
                + rewrite MapsPtes.F.not_find_in_iff in H3.
                  rewrite H3;reflexivity. }
          * rewrite add_multiple_comm;reflexivity.
      - setoid_replace m'' with (add_multiple k e m').
        + reflexivity.
        + replace (add_multiple k e m') with (Maps.add k e m').
          * apply H1.
          * unfold add_multiple,multiplicity.
            rewrite MapsPtes.F.not_find_in_iff in H0.
            rewrite H0;reflexivity. }
  Qed.

  Lemma union_rec_left : forall a ms ms', eq (union (add a ms) ms') (add a (union ms ms')).
  Proof.
    intros a ms ms'.
    repeat rewrite add_add_multiple.
    unfold eq,union,add.
    apply addm_rec_left.
  Qed.

  Lemma addm_rec_right :
    forall (m1 m2: Maps.t nat) (k : Maps.key) (e : nat),
      eq (Maps.fold add_multiple m1 (add_multiple k e m2)) (add_multiple k e (Maps.fold add_multiple m1 m2)).
  Proof.
    intros m1 m2.
    setoid_rewrite eq_Equal.
    assert (morph:
              forall (ms1 : Maps.t nat)
                     (ms1' : Maps.t nat)
                     (H1 : Maps.Equal ms1 ms1')
                     (ms2 : Maps.t nat)
                     (ms2' : Maps.t nat)
                     (H2 : Maps.Equal ms2 ms2'),
                Maps.Equal (Maps.fold add_multiple ms1 ms2) (Maps.fold add_multiple ms1' ms2')).
    { clear.
      apply fold_pseudo_morph.
      intros k k' n ms0 ms'0 H H0.
      apply add_multiple_morph;trivial.
      apply add_multiple_morph_Proper.
      apply transpose_neqkey_equal_add_multiple.
      intros k e a k' H.
      unfold add_multiple,multiplicity.
      destruct (Maps.find k a).
      apply MapsPtes.F.add_neq_o;trivial.
      apply MapsPtes.F.add_neq_o;trivial. }
    
    pattern m1,(Maps.fold add_multiple m1 m2).
    apply MapsPtes.fold_rec.

    { intros m H k e.
      rewrite MapsPtes.fold_Empty;auto with *. }

    { intros k e a m' m'' H H0 H1 H2 k0 e0.
      rewrite morph with (ms1':= (add_multiple k e m'))
                           (ms2':=(add_multiple k0 e0 m2));trivial; try reflexivity.
      rewrite MapsPtes.fold_Add with (k:=k) (e:=e) (m1:= m');auto with *.
      rewrite H2.
      apply add_multiple_comm.
      apply transpose_neqkey_equal_add_multiple.
      unfold add_multiple,multiplicity.
      rewrite (MapsPtes.F.not_find_in_iff m' k) in H0.
      rewrite H0.
      red;tauto.
      unfold add_multiple,multiplicity.
      rewrite (MapsPtes.F.not_find_in_iff m' k) in H0.
      rewrite H0.
      exact H1. }
  Qed.

  Lemma union_rec_right : forall a ms ms', eq (union ms (add a ms')) (add a (union ms ms')).
  Proof.
    intros a ms ms'.
    repeat rewrite add_add_multiple.
    unfold eq,union,add.
    apply addm_rec_right.
  Qed.

  Lemma mem_morph_eq :
    forall (φ : A) (Γ Γ' : t), eq Γ Γ' -> mem φ Γ = mem φ Γ'.
  Proof.
    intros φ Γ Γ' H.
    unfold eq,mem in *.
    apply  MapsPtes.F.mem_m.
    reflexivity.
    assumption.
  Qed.


  Lemma eq_bool_correct : forall m1 m2, eq_bool m1 m2 = true -> eq m1 m2.
  Proof.
    unfold eq,eq_bool.
    intros m1 m2 H.
    apply Maps.equal_2 in H.
    rewrite <- MapsPtes.F.Equal_Equivb in H. 
    assumption.
    clear m1 m2 H.
    intros m n.
    functional induction (nat_eq_bool m n).
    tauto.
    split;intro H;destruct IHb.
    rewrite (H0 H);reflexivity.
    injection H;clear H;intro H.
    auto.
    destruct n;destruct m;try tauto;
    split;intro;discriminate.
  Qed.

  Lemma eq_bool_complete : forall m1 m2, eq m1 m2 -> eq_bool m1 m2 = true.
  Proof.
    unfold eq,eq_bool.
    intros m1 m2 H.
    apply Maps.equal_1. 
    rewrite <- MapsPtes.F.Equal_Equivb . 
    assumption.
    clear m1 m2 H.
    intros m n.
    functional induction (nat_eq_bool m n).
    tauto.
    split;intro H;destruct IHb.
    rewrite (H0 H);reflexivity.
    injection H;clear H;intro H.
    auto.
    destruct n;destruct m;try tauto;
    split;intro;discriminate.
  Qed.
  
  Lemma remove_empty : forall φ, remove φ empty = empty.
  Proof.
    intros φ.
    unfold remove,empty,multiplicity.
    rewrite MapsFact.empty_o.
    reflexivity.
  Qed.

  Lemma remove_same_add : forall φ φ' Γ, X.eq φ φ' -> eq (remove φ (add φ' Γ)) Γ.
  Proof.
    intros φ φ' Γ H.
    unfold remove,add,add_multiple,multiplicity.
    rewrite eq_Equal.
    case_eq (Maps.find φ' Γ).

    intros n Heq.
    rewrite MapsFact.add_eq_o.    
    simpl.
    rewrite MapsFact.Equal_mapsto_iff.
    intros k e.
    split;intro.
    rewrite MapsFact.add_mapsto_iff in H0.
    destruct H0.
    destruct H0;subst.
    apply Maps.find_2.
    rewrite <- (MapsPtes.F.find_o _ H0).
    rewrite  (MapsPtes.F.find_o _ H).
    assumption.
    destruct H0.
    apply Maps.add_3 in H1.
    assumption.
    intro;elim H0;apply X.eq_trans with φ'.
    assumption.
    exact H2.
    case (X.eq_dec φ k);intros.
    replace e with n.
    apply Maps.add_1.
    assumption.
    rewrite MapsFact.find_mapsto_iff in H0.
    rewrite <- (MapsFact.find_o _ e0) in H0.
    rewrite (MapsFact.find_o _ H) in H0.
    rewrite H0 in Heq;injection Heq;clear Heq;auto.
    apply Maps.add_2.
    assumption.
    apply Maps.add_2.
    intro;elim n0;apply X.eq_trans with φ';assumption.
    assumption.
    symmetry.
    auto.

    intros Heq.
    rewrite MapsFact.add_eq_o.    
    rewrite MapsFact.Equal_mapsto_iff.
    intros k e.
    case (X.eq_dec k φ);intros Heq'.
    split;intro.
    apply Maps.find_1 in H0.
    rewrite MapsFact.remove_eq_o in H0.
    discriminate.
    symmetry;assumption.
    rewrite MapsPtes.F.find_mapsto_iff in H0.    
    rewrite (MapsPtes.F.find_o _ Heq') in H0.
    rewrite (MapsPtes.F.find_o _ H) in H0.
    rewrite Heq in H0;discriminate.
    do 2 rewrite MapsPtes.F.find_mapsto_iff.    
    rewrite MapsPtes.F.remove_neq_o.
    rewrite MapsPtes.F.add_neq_o.
    tauto.
    intro;elim Heq';apply X.eq_trans with φ'.
    symmetry;assumption.
    symmetry;assumption.
    intro;elim Heq'; symmetry;assumption.
    symmetry;assumption.
  Qed.

  Lemma remove_same_add_in : forall φ φ' Γ,
                               X.eq φ φ'
                               -> Maps.In φ' Γ
                               -> eq (add φ (remove φ' Γ)) Γ.
  Proof.
    intros φ φ' Γ H.
    unfold remove,add,add_multiple,multiplicity.
    rewrite eq_Equal.
    
    case_eq (Maps.find φ' Γ).
    - intros n H0 H1.
      simpl.
      setoid_rewrite H.
      destruct n.
      + rewrite MapsFact.remove_eq_o.
        * hnf.
          intros y.
          { destruct (X.eq_dec y φ').
            - rewrite e.
              rewrite MapsFact.add_eq_o;auto.
            - rewrite MapsFact.add_neq_o;auto.
              rewrite MapsFact.remove_neq_o;auto. }
        * reflexivity.
      + rewrite MapsFact.add_eq_o;auto.
        rewrite add_add_add;auto.
        hnf.
        intros y.
        { destruct (X.eq_dec y φ').
          - rewrite e.
            rewrite MapsFact.add_eq_o;auto.
          - rewrite MapsFact.add_neq_o;auto.
        }
    - intros H0 H1.
      rewrite MapsFact.in_find_iff in H1.
      contradiction.
  Qed.



  Lemma remove_diff_add : forall φ φ' Γ, ~X.eq φ φ' -> 
                                         eq (remove φ (add φ' Γ)) (add φ' (remove φ Γ)).
  Proof.
    intros φ φ' Γ H.
    repeat rewrite add_add_multiple.
    unfold remove,add,add_multiple,multiplicity.
    rewrite eq_Equal.
    simpl.
    case_eq (Maps.find φ' Γ);
      [intros n|]; intros Heq;
      (case_eq (Maps.find φ Γ);
       [intros n'|];intros Heq').
    destruct n'.

    { rewrite MapsFact.add_neq_o;[|intro;elim H;symmetry;assumption].    
      rewrite Heq'.
      rewrite MapsFact.remove_neq_o;[| assumption].
      rewrite Heq.
      rewrite MapsFact.Equal_mapsto_iff.
      intros k e.
      do 2 rewrite MapsFact.find_mapsto_iff.
      case (X.eq_dec k φ); case (X.eq_dec k φ');intros Heq1 Heq2.
      elim H;apply X.eq_trans with k.
      symmetry;assumption.
      assumption.
      rewrite MapsFact.remove_eq_o;[|symmetry;assumption ].
      rewrite MapsFact.add_neq_o;[|intro;elim Heq1;symmetry;assumption ].
      rewrite MapsFact.remove_eq_o;[|symmetry;assumption ].
      reflexivity.
      rewrite MapsFact.remove_neq_o;[|intro;elim Heq2;symmetry;assumption ].
      rewrite MapsFact.add_eq_o;[|symmetry;assumption ].
      rewrite MapsFact.add_eq_o;[|symmetry;assumption ].
      reflexivity.
      rewrite MapsFact.remove_neq_o;[|intro;elim Heq2;symmetry;assumption ].
      rewrite MapsFact.add_neq_o;[|intro;elim Heq1;symmetry;assumption ].
      rewrite MapsFact.add_neq_o;[|intro;elim Heq1;symmetry;assumption ].
      rewrite MapsFact.remove_neq_o;[|intro;elim Heq2;symmetry;assumption ].
      reflexivity. }

    { rewrite MapsFact.add_neq_o;[|intro;elim H;symmetry;assumption].    
      rewrite Heq'.
      rewrite MapsFact.add_neq_o;[| assumption].
      rewrite Heq.
      rewrite MapsFact.Equal_mapsto_iff.
      intros k e.
      do 2 rewrite MapsFact.find_mapsto_iff.
      case (X.eq_dec k φ); case (X.eq_dec k φ');intros Heq1 Heq2.
      elim H;apply X.eq_trans with k.
      symmetry;assumption.
      assumption.
      rewrite MapsFact.add_eq_o;[|symmetry;assumption ].
      rewrite MapsFact.add_neq_o;[|intro;elim Heq1;symmetry;assumption ].
      rewrite MapsFact.add_eq_o;[|symmetry;assumption ].
      reflexivity.
      rewrite MapsFact.add_neq_o;[|intro;elim Heq2;symmetry;assumption ].
      rewrite MapsFact.add_eq_o;[|symmetry;assumption ].
      rewrite MapsFact.add_eq_o;[|symmetry;assumption ].
      reflexivity.
      rewrite MapsFact.add_neq_o;[|intro;elim Heq2;symmetry;assumption ].
      rewrite MapsFact.add_neq_o;[|intro;elim Heq1;symmetry;assumption ].
      rewrite MapsFact.add_neq_o;[|intro;elim Heq1;symmetry;assumption ].
      rewrite MapsFact.add_neq_o;[|intro;elim Heq2;symmetry;assumption ].
      reflexivity. }

    { rewrite MapsFact.add_neq_o;[|intro;elim H;symmetry;assumption].    
      rewrite Heq.
      rewrite Heq'.
      apply MapsPtes.F.Equal_refl. }



    rewrite MapsFact.add_neq_o;[|intro;elim H;symmetry;assumption].    
    rewrite Heq'.
    destruct n'.

    { rewrite MapsFact.remove_neq_o;[|intro;elim H;assumption].    
      rewrite Heq.
      rewrite MapsFact.Equal_mapsto_iff.
      intros k e.
      do 2 rewrite MapsFact.find_mapsto_iff.
      case (X.eq_dec k φ); case (X.eq_dec k φ');intros Heq1 Heq2.
      elim H;apply X.eq_trans with k.
      symmetry;assumption.
      assumption.
      rewrite MapsFact.add_neq_o;[|intro;elim Heq1;symmetry;assumption ].
      rewrite MapsFact.remove_eq_o;[|symmetry;assumption ].
      rewrite MapsFact.remove_eq_o;[|symmetry;assumption ].
      reflexivity.
      rewrite MapsFact.remove_neq_o;[|intro;elim Heq2;symmetry;assumption ].
      rewrite MapsFact.add_eq_o;[|symmetry;assumption ].
      rewrite MapsFact.add_eq_o;[|symmetry;assumption ].
      reflexivity.
      rewrite MapsFact.remove_neq_o;[|intro;elim Heq2;symmetry;assumption ].
      rewrite MapsFact.add_neq_o;[|intro;elim Heq1;symmetry;assumption ].
      rewrite MapsFact.add_neq_o;[|intro;elim Heq1;symmetry;assumption ].
      rewrite MapsFact.remove_neq_o;[|intro;elim Heq2;symmetry;assumption ].
      reflexivity. }

    { rewrite MapsFact.add_neq_o;[|intro;elim H;assumption].    
      rewrite Heq.
      rewrite MapsFact.Equal_mapsto_iff.
      intros k e.
      do 2 rewrite MapsFact.find_mapsto_iff.
      case (X.eq_dec k φ); case (X.eq_dec k φ');intros Heq1 Heq2.
      elim H;apply X.eq_trans with k.
      symmetry;assumption.
      assumption.
      rewrite MapsFact.add_eq_o;[|symmetry;assumption ].
      rewrite MapsFact.add_neq_o;[|intro;elim Heq1;symmetry;assumption ].
      rewrite MapsFact.add_eq_o;[|symmetry;assumption ].
      reflexivity.
      rewrite MapsFact.add_neq_o;[|intro;elim Heq2;symmetry;assumption ].
      rewrite MapsFact.add_eq_o;[|symmetry;assumption ].
      rewrite MapsFact.add_eq_o;[|symmetry;assumption ].
      reflexivity.
      rewrite MapsFact.add_neq_o;[|intro;elim Heq2;symmetry;assumption ].
      rewrite MapsFact.add_neq_o;[|intro;elim Heq1;symmetry;assumption ].
      rewrite MapsFact.add_neq_o;[|intro;elim Heq1;symmetry;assumption ].
      rewrite MapsFact.add_neq_o;[|intro;elim Heq2;symmetry;assumption ].
      reflexivity. }

    { rewrite MapsFact.add_neq_o;[|intro;elim H;symmetry;assumption  ].    
      rewrite Heq.
      rewrite Heq'.
      reflexivity. }
  Qed.
  
  Lemma is_empty_morph_eq : forall (Γ Γ' : t), eq Γ Γ' -> is_empty Γ = is_empty Γ'.
  Proof.
    unfold eq,is_empty.
    apply MapsFact.is_empty_m.
  Qed.
  
  Lemma remove_morph_eq : 
    forall a a', X.eq a a' -> forall ms ms',  eq ms ms' -> eq (remove a ms) (remove a' ms'). 
  Proof.
    intros a a' H ms ms' H0.
    unfold remove,multiplicity in *.
    rewrite eq_Equal.
    repeat setoid_rewrite H.
    repeat setoid_rewrite H0.
    case (Maps.find a' ms');[intros n;destruct n|];
    repeat setoid_rewrite H;
    repeat setoid_rewrite H0;reflexivity.
  Qed.


  Lemma mem_union_l : forall a ms ms', mem a ms = true -> mem a (union ms ms') = true.
  Proof.
    intros a ms ms'.
    unfold mem,union,multiplicity.
    apply MapsPtes.fold_rec.

    { intros m H H0.
      apply Maps.mem_2 in H0.
      rewrite MapsPtes.F.in_find_iff in H0.
      rewrite Empty_not_find in H0.
      elim H0;reflexivity.
      assumption. }

    {
      intros k e a0 m' m'' H H0 H1 H2 H3.
      unfold mem,add,add_multiple,multiplicity.
      destruct (Maps.find k a0).    
      case (X.eq_dec a k);intros heq.
      rewrite MapsPtes.F.add_eq_b;auto.
      rewrite MapsPtes.F.add_neq_b;auto.
      apply H2.
      red in H1.
      generalize (H1 a).
      rewrite (MapsFact.mem_find_b) in H3. 
      destruct (Maps.find a m'');try discriminate.
      rewrite MapsPtes.F.add_neq_o.
      rewrite MapsFact.mem_find_b.
      intros.
      rewrite <- H4.
      reflexivity.
      auto.
      case (X.eq_dec a k);intros heq.
      rewrite MapsPtes.F.add_eq_b;auto.
      rewrite MapsPtes.F.add_neq_b;auto.
      apply H2.
      red in H1.
      generalize (H1 a).
      rewrite (MapsFact.mem_find_b) in H3. 
      destruct (Maps.find a m'');try discriminate.
      rewrite MapsPtes.F.add_neq_o.
      rewrite MapsFact.mem_find_b.
      intros.
      rewrite <- H4.
      reflexivity.
      auto. }
  Qed.

  Lemma mem_union_r : forall a ms ms', mem a ms' = true -> mem a (union ms ms') = true.
  Proof.
    intros a ms ms'.
    unfold mem,union,multiplicity.
    apply MapsPtes.fold_rec.

    { tauto. }

    { intros k e a0 m' m'' H H0 H1 H2 H3.
      unfold mem,add,add_multiple,multiplicity.
      destruct (Maps.find k a0).    
      case (X.eq_dec a k);intros heq.
      rewrite MapsPtes.F.add_eq_b;auto.
      rewrite MapsPtes.F.add_neq_b;auto.
      case ( X.eq_dec a k);intros.
      apply  MapsPtes.F.add_eq_b;auto.
      rewrite MapsPtes.F.add_neq_b;auto. }
  Qed.

  Lemma mem_union_destruct : forall a ms ms', mem a (union ms ms') = true -> mem a ms = true \/mem a ms' = true.
  Proof.
    intros a ms ms'.
    unfold mem,union,add_multiple,multiplicity.
    apply MapsPtes.fold_rec.

    { tauto. }

    { intros k e a0 m' m''. 
      case (Maps.find k a0).
      intros n H H0 H1 H2 H3.
      case (X.eq_dec a k);intros heq.
      red in H1.
      rewrite MapsPtes.F.mem_find_b.
      rewrite H1.
      rewrite MapsPtes.F.add_eq_o;auto.
      rewrite MapsPtes.F.add_neq_b in H3;auto.
      destruct (H2 H3);auto.
      left.
      red in H1.
      rewrite MapsPtes.F.mem_find_b.
      rewrite H1.
      rewrite MapsPtes.F.add_neq_o;auto.
      rewrite <- MapsPtes.F.mem_find_b;auto.
      intros H H0 H1 H2 H3.
      case (X.eq_dec a k);intros heq.
      red in H1.
      rewrite MapsPtes.F.mem_find_b.
      rewrite H1.
      rewrite MapsPtes.F.add_eq_o;auto.
      rewrite MapsPtes.F.add_neq_b in H3;auto.
      destruct (H2 H3);auto.
      left.
      red in H1.
      rewrite MapsPtes.F.mem_find_b.
      rewrite H1.
      rewrite MapsPtes.F.add_neq_o;auto.
      rewrite <- MapsPtes.F.mem_find_b;auto. }
  Qed.


  Lemma mem_remove_1 : forall a b ms, ~X.eq a b -> mem a ms = mem a (remove b ms).
  Proof.
    intros a b ms.
    unfold mem,remove,multiplicity.
    intros H.
    case (Maps.find b ms).
    intros [ | n].
    rewrite MapsPtes.F.remove_neq_b;auto.
    rewrite MapsPtes.F.add_neq_b;auto.
    auto.
  Qed.

  Lemma mem_remove_2 : forall a b ms, mem a (remove b ms) = true  -> mem a ms=true.
  Proof.
    intros a b ms.
    unfold mem,remove,multiplicity.
    case_eq (Maps.find b ms);[intros n H|intros H].
    destruct n as [ | n].
    case (X.eq_dec a b);intros heq.
    rewrite MapsPtes.F.remove_eq_b;auto;discriminate.
    rewrite MapsPtes.F.remove_neq_b;auto.
    case (X.eq_dec a b);intros heq.
    intros _.
    rewrite MapsPtes.F.mem_find_b.
    rewrite <- (@MapsPtes.F.find_o _ _ _  _ heq) in H.
    rewrite H;reflexivity.
    rewrite MapsPtes.F.add_neq_b;auto.
    tauto.
  Qed.

  Lemma eq_mem : forall ms ms', eq ms ms' -> (forall a, mem a ms = mem a ms').
  Proof.
    unfold mem.
    setoid_rewrite eq_Equal.
    intros ms ms'.
    intros H a.
    rewrite H.
    reflexivity.
  Qed.

  (* Reserved Notation "∪" (at level 60, right associativity). *)
  Reserved Notation "∅" (at level 0, no associativity).

  Declare Scope multiset_scope.
  Infix "∪" := union (at level 65, right associativity) : multiset_scope.
  Notation " a :: b " := (add a b) (at level 60, right associativity) : multiset_scope.
  Notation "[ a , .. , b ]" := (add a .. (add b empty) ..) (at level 40): multiset_scope.
  Notation "∅" := (empty) : multiset_scope.
  Notation " E == F " := (eq E F) (at level 80): multiset_scope.

  (* Notation pour l'appartenance à un environnement. *)
  Notation " x ∈ F " := (In x F) (at level 55): multiset_scope.

  Notation " b '\' a " := (remove a b) (at level 64, right associativity) : multiset_scope.
  Open Scope multiset_scope.
  
  Lemma multiset_ind : forall (P:t -> Type), (forall Γ Γ', Γ==Γ' -> P Γ -> P Γ') -> P empty -> (forall x Γ, P Γ -> P (x::Γ)) -> forall Γ, P Γ.
  Proof.
    intros P X X0 X1 Γ.
    induction Γ using MapsPtes.map_induction_bis.
    - eauto.
    - apply X0.
    - induction e as [| n].  
      + generalize (X1 x Γ IHΓ).
        unfold add,add_multiple,multiplicity.
        rewrite MapsPtes.F.not_find_in_iff in H;rewrite H.
        tauto.
      + generalize (X1 x _ IHn).
        unfold add,add_multiple,multiplicity.
        rewrite MapsPtes.F.add_eq_o;[|apply X.eq_refl].
        clear - X;intros.
        assert ((Maps.add x (S n) (Maps.add x n Γ)) == (Maps.add x (S n) Γ)).
        { intros y.
          unfold multiplicity.
          case (X.eq_dec y x);intros Heq.
          rewrite Heq; do 2 (rewrite MapsPtes.F.add_eq_o;[|apply X.eq_refl]);
          reflexivity.
          do 3 (rewrite MapsPtes.F.add_neq_o
                ;[|intros abs;elim Heq;apply X.eq_sym;exact abs]);reflexivity. }
        apply (X _ _ H);assumption.
  Qed.

  Lemma env_decomp : ∀ Γ, (Γ == ∅)\/exists φ, exists Γ', Γ==φ::Γ'.
  Proof.
    intros Γ.
    induction Γ using multiset_ind.
    - destruct IHΓ1.
      + left;rewrite H in H0;assumption.
      + right;destruct H0 as [φ [Γ' H1]];exists φ;exists Γ'.
        rewrite H in H1;assumption.
    - left;reflexivity.
    - right.
      exists x.
      exists Γ.
      reflexivity.
  Qed.

  Add Relation t eq
      reflexivity proved by eq_refl
      symmetry proved by eq_sym
      transitivity proved by eq_trans as eq_rel.

  (* On peut réécrire à l'intérieur d'un ::. *)
  Add Morphism add
      with signature (X.eq ==> eq ==> eq)
        as add_morph.
  Proof.
    exact add_morph_eq.
  Qed.
  
  (* On peut réécrire à l'intérieur d'une union d'environnements. *)
  Add Morphism union
      with signature (eq==> eq ==> eq)
        as union_morph.
  Proof.
    exact union_morph_eq.
  Qed.

  (* On peut réécrire à l'intérieur d'un mem. *)
  Add Morphism mem
      with signature ( Logic.eq ==> eq ==> Logic.eq)
        as mem_morph.
  Proof.
    apply mem_morph_eq.
  Qed.



  Lemma add_singleton_abs : 
    ∀ φ φ' φ'' Γ, φ'::φ''::Γ == [φ] -> False.
  Proof.
    intros φ φ' φ'' Γ H.
    case (X.eq_dec φ φ');intros Heq1.
    rewrite <- Heq1 in H;clear Heq1.
    case (X.eq_dec φ φ'');intros Heq2.
    rewrite <- Heq2 in H;clear Heq2.
    - clear -H .
      assert (u:=H φ);clear H.
      unfold add,add_multiple,multiplicity in u.
      rewrite MapsPtes.F.empty_o in u.
      rewrite MapsPtes.F.add_eq_o in u by apply X.eq_refl.
      destruct (Maps.find (elt:=nat) φ Γ) .
      + rewrite MapsPtes.F.add_eq_o in u by apply X.eq_refl.
        rewrite MapsPtes.F.add_eq_o in u by apply X.eq_refl.
        discriminate.
      + rewrite MapsPtes.F.add_eq_o in u by apply X.eq_refl.
        rewrite MapsPtes.F.add_eq_o in u by apply X.eq_refl.
        discriminate.
    - assert (u:=H φ'');clear -u Heq2.
      unfold add,add_multiple,multiplicity in u.
      rewrite MapsPtes.F.empty_o in u.
      setoid_rewrite MapsPtes.F.add_neq_o in u;
        try now (intros abs;elim Heq2;rewrite abs;apply X.eq_refl).
      rewrite MapsPtes.F.empty_o in u.
      destruct (Maps.find (elt:=nat) φ'' Γ) .
      + rewrite MapsPtes.F.add_eq_o in u by apply X.eq_refl.
        discriminate.
      + rewrite MapsPtes.F.add_eq_o in u by apply X.eq_refl.
        discriminate.
    - assert (u:=H φ');clear -u Heq1.
      unfold add,add_multiple,multiplicity in u.
      rewrite MapsPtes.F.empty_o in u.
      setoid_rewrite MapsPtes.F.add_neq_o at 3 in u; try now (intros abs;elim Heq1;rewrite abs;apply X.eq_refl).
      rewrite MapsPtes.F.empty_o in u.
      destruct (Maps.find (elt:=nat) φ'' Γ) .
      + case (X.eq_dec φ' φ'');intros Heq2.
        * rewrite Heq2 in *.
          rewrite MapsPtes.F.add_eq_o in u; try now (symmetry).
          rewrite MapsPtes.F.add_eq_o in u; try now (symmetry).
          discriminate.   
        * setoid_rewrite MapsPtes.F.add_neq_o at 2 in u; try now (intros abs;elim Heq2;rewrite abs;apply X.eq_refl).
          { destruct (Maps.find (elt:=nat) φ' Γ) .
            - rewrite MapsPtes.F.add_eq_o in u by apply X.eq_refl.
              discriminate.
            - rewrite MapsPtes.F.add_eq_o in u by apply X.eq_refl.
              discriminate. }

      + case (X.eq_dec φ' φ'');intros Heq2.
        * rewrite MapsPtes.F.add_eq_o in u ; try now (symmetry;symmetry).
          rewrite MapsPtes.F.add_eq_o in u ; try now symmetry;auto.
          discriminate.   
        * setoid_rewrite MapsPtes.F.add_neq_o in u at 2 ; try now (intros abs;elim Heq2;rewrite abs;apply X.eq_refl).
          { destruct (Maps.find (elt:=nat) φ' Γ) .
            - rewrite MapsPtes.F.add_eq_o in u by apply X.eq_refl.
              discriminate.
            - rewrite MapsPtes.F.add_eq_o in u by apply X.eq_refl.
              discriminate. } 
  Qed.


  
  Lemma union_singleton_decompose : 
    ∀ Δ Δ' φ, Δ∪Δ' == [φ] -> (Δ==[φ]/\Δ'==∅)\/(Δ'==[φ]/\Δ==∅).
  Proof.
    intros Δ Δ' φ H.
    destruct (env_decomp Δ).
    right;split;auto.
    rewrite H0 in H. 
    rewrite union_empty_left in H;exact H.
    destruct H0 as [φ' [Γ' H1]].
    destruct (env_decomp Γ').
    rewrite H0 in H1;clear H0.
    left.
    destruct (env_decomp Δ').
    split;auto.   
    rewrite H1 in H;rewrite H0 in H;rewrite H1;
    rewrite union_empty_right in H;auto.
    destruct H0 as [φ'' [Γ'' H2]].
    apply False_ind.   
    rewrite H1 in H;rewrite H2 in H.
    clear -H.
    rewrite union_rec_right in H.
    rewrite union_rec_left in H.
    apply add_singleton_abs with (1:=H).
    
    rewrite H1 in H;clear H1.
    destruct H0 as [φ'' [Γ'' H1]].
    rewrite H1 in H;clear H1.
    rewrite union_rec_left in H.
    rewrite union_rec_left in H.
    elim add_singleton_abs with (1:=H).
  Qed.

  Lemma mem_decompose : 
    forall Γ φ, mem φ Γ = true -> exists Γ', Γ == φ :: Γ'.
  Proof.
    intros Γ. 
    induction Γ using multiset_ind. 

    intros φ H0.
    rewrite <- H in H0.
    destruct (IHΓ1 _ H0) as [Γ' H1].
    exists Γ';rewrite H in H1;assumption.

    intros φ H.
    unfold mem in H;rewrite MapsPtes.F.empty_a in H;discriminate.

    intros φ H.
    destruct (mem_destruct _ _ _ H) as [H1|H1];clear H.
    exists Γ;rewrite H1;reflexivity.
    destruct (IHΓ _ H1) as [Γ' H2];clear H1.
    exists (x::Γ').
    rewrite H2.
    rewrite add_comm;reflexivity.
  Qed.

  Lemma In_decompose : 
    forall Γ φ, φ ∈ Γ -> exists Γ', Γ == φ :: Γ'.
  Proof.
    intros Γ φ h.
    apply mem_in_iff in h.
    apply mem_decompose.
    assumption.
  Qed.

  Lemma eq_add_inject : 
    ∀ φ Γ Γ', φ::Γ == φ::Γ' -> Γ == Γ'.
  Proof.
    intros φ Γ Γ' H.
    red in H.   
    intro ψ.
    case (X.eq_dec ψ φ);intro Heq.
    rewrite Heq.
    generalize (H φ).
    unfold add,add_multiple,multiplicity.
    case (Maps.find φ Γ);case (Maps.find φ Γ');simpl;try reflexivity;intros.
    setoid_rewrite MapsPtes.F.add_eq_o in H0;auto.
    f_equal. injection H0;tauto.
    do 2 (rewrite MapsPtes.F.add_eq_o in H0;[|apply X.eq_refl]);discriminate.
    do 2 (rewrite MapsPtes.F.add_eq_o in H0;[|apply X.eq_refl]);discriminate.
    generalize (H ψ).
    unfold add,add_multiple,multiplicity.
    case (Maps.find φ Γ);case (Maps.find φ Γ');simpl;try reflexivity;intros.
    do 2 (rewrite MapsPtes.F.add_neq_o in H0;[|intros abs;elim Heq;rewrite abs;apply X.eq_refl]);assumption.
    do 2 (rewrite MapsPtes.F.add_neq_o in H0;[|intros abs;elim Heq;rewrite abs;apply X.eq_refl]);assumption.
    do 2 (rewrite MapsPtes.F.add_neq_o in H0;[|intros abs;elim Heq;rewrite abs;apply X.eq_refl]);assumption.
    do 2 (rewrite MapsPtes.F.add_neq_o in H0;[|intros abs;elim Heq;rewrite abs;apply X.eq_refl]);assumption.
  Qed.

  Lemma union_sym : ∀ Γ Γ', Γ∪Γ' == Γ'∪Γ.
  Proof.
    intros Γ.
    induction Γ using multiset_ind.

    intros Γ'.
    rewrite <- H;auto.
    intros Γ'.
    rewrite union_empty_right;rewrite union_empty_left;reflexivity.   

    intros Γ'.
    rewrite union_rec_right;rewrite union_rec_left; rewrite IHΓ;reflexivity.
  Qed.

  Lemma union_decompose : 
    ∀ Γ Δ Δ' φ, Δ∪Δ' == φ::Γ -> 
                (exists Δ0, Δ == φ :: Δ0 /\ Δ0∪Δ' == Γ)\/
                (exists Δ0, Δ' == φ :: Δ0 /\ Δ0∪Δ == Γ).
  Proof.
    intros Γ.
    
    induction Γ using multiset_ind.
    intros Δ Δ' φ H0.   
    rewrite <- H in H0.
    destruct (IHΓ1 _ _ _ H0) as [[Δ0 H1]|[Δ0 H1]].
    left;exists Δ0;rewrite H in H1;assumption.
    right;exists Δ0;rewrite H in H1;assumption.

    intros Δ Δ' φ H.
    destruct (union_singleton_decompose _ _ _ H) as [H1|H1];[left|right];
    exists empty;rewrite union_empty_left;assumption.

    intros Δ Δ' φ H. 
    assert (H':=eq_mem _ _ H  φ).
    rewrite add_is_mem in H';[|apply X.eq_refl]. 
    destruct (mem_union_destruct _ _ _ H') as [H1|H1];clear H'.
    destruct (mem_decompose _ _ H1) as [Δ0 H2];clear H1.
    left;exists Δ0;split;auto.
    rewrite H2 in H.
    rewrite union_rec_left in H.
    assert (H':=eq_add_inject _ _ _ H);clear H;assumption.
    destruct (mem_decompose _ _ H1) as [Δ0 H2];clear H1.
    right;exists Δ0;split;auto.
    rewrite H2 in H.
    rewrite union_rec_right in H.
    assert (H':=eq_add_inject _ _ _ H);clear H. 
    rewrite union_sym;assumption.
  Qed.
  
  Lemma union_empty_decompose : ∀ Δ Δ', Δ∪Δ'== ∅ -> Δ==∅/\Δ'==∅.
  Proof.
    intros Δ.
    induction Δ using multiset_ind.
    
    intros; rewrite <- H; rewrite <- H in H0;auto.

    intros Δ' H.
    rewrite union_empty_left in H;split;auto.
    reflexivity.

    intros Δ' H.
    clear -H.
    apply False_ind.
    unfold eq,Maps.Equal,multiplicity in H.
    generalize (H x).
    rewrite MapsPtes.F.empty_o.
    rewrite union_rec_left.
    unfold add,add_multiple,multiplicity.
    case (Maps.find x (Δ∪Δ'));[intro|];
    (rewrite MapsPtes.F.add_eq_o;[discriminate|apply X.eq_refl]).
  Qed.

  Lemma is_empty_eq_empty : ∀ Γ, is_empty Γ = true -> Γ == empty.
  Proof.
    intro.
    induction Γ using multiset_ind.

    rewrite <- H;assumption.

    reflexivity.

    clear;intro abs.
    unfold is_empty,add,add_multiple,multiplicity in abs.
    destruct (Maps.find x Γ);  apply Maps.is_empty_2 in abs.
    red in abs.
    elim (abs x (S n)).
    apply Maps.add_1;reflexivity.
    red in abs.
    elim (abs x 0);  apply Maps.add_1;reflexivity.
  Qed.


  Lemma add_maps_add : ∀ Γ k n, ~(Maps.In k Γ) -> 
                                (Maps.add k n Γ) == iter _ (fun k acc => k::acc) k n Γ.
  Proof.
    intros Γ k n.

    induction n;intros.

    simpl. unfold add,add_multiple,multiplicity.
    rewrite MapsFact.not_find_in_iff in H;rewrite H.
    reflexivity.

    simpl.
    rewrite <- IHn;auto.
    unfold add,add_multiple,multiplicity.
    rewrite MapsPtes.F.add_eq_o;[|apply X.eq_refl].
    intro y.
    unfold multiplicity.
    case (X.eq_dec k y);intros Heq.
    do 2 (rewrite MapsPtes.F.add_eq_o;[|assumption]);reflexivity.
    do 3 (rewrite MapsPtes.F.add_neq_o;[|intros abs;elim Heq;rewrite abs;apply X.eq_refl]);reflexivity.
  Qed.

  Lemma fold_rec_weak:
    ∀ (B : Type) (P : t → B → Type) (f : A → B → B)
      (i : B),
      (∀ (m m' : t) (a : B),  m == m' → P m a → P m' a)
      → P empty i
      → (∀ k a (m : t),
           P m a → P (add k m) (f k a))
      → (∀ m : t, P m (fold _ f m i))
  .
  Proof.
    intros B P f i X X0 X1 m.
    unfold fold.
    apply MapsPtes.fold_rec_weak.

    assumption.

    assumption.

    intros k e a m0 H X2.
    apply (X _ _ _ (eq_sym _ _ (add_maps_add _ _ e H))).
    clear -X1 X2.
    induction e.
    simpl.
    auto.
    simpl;auto.
  Qed.

  Lemma multiset_Ind :
    forall (P:t -> Type),
      (forall Γ, Empty Γ -> P Γ)
      -> (forall x e Γ Γ', P Γ -> ~ In x Γ -> Add_multiple x e Γ Γ' -> P Γ')
      -> forall Γ, P Γ.
  Proof.
    intros P X X0 Γ.
    induction Γ using MapsPtes.map_induction.
    - apply X.
      assumption.
    - eapply X0.
      + exact IHΓ1.
      + exact H.
      + unfold Add_multiple, multiplicity in *.
        unfold MapsPtes.Add in H0.
        intros y.
        unfold add_multiple.
        rewrite MapsFact.not_find_in_iff in H.
        unfold multiplicity.
        rewrite H.
        apply H0.
  Qed.        



  Definition transpose_neqkey (B:Type) (eqB:B -> B -> Prop) (f:A -> B -> B)  := 
    ∀ (k k' : A) (a : B),
      (*¬X.eq k k' → *)eqB (f k (f k' a)) (f k' (f k a)).

  Lemma iter_proper : 
    ∀ (B : Type) (eqB : B → B → Prop),
    ∀ f : A  → B → B,
      Proper (X.eq ==> eqB ==> eqB) f -> 
      Proper (X.eq ==> Logic.eq ==> eqB ==> eqB) (iter B f).
  Proof.
    intros B eqB f H.
    repeat red.
    intros x y H1 x0 y0 H2 x1 y1 H3.
    subst.
    revert x y H1 x1 y1 H3.
    induction y0 as [ | n];intros;simpl.
    apply H;assumption.
    apply H;try assumption.
    auto.
  Qed.

  Lemma iter_transpose_neqkey : 
    ∀ (B : Type) (eqB : B → B → Prop),
      Equivalence eqB ->
      ∀ f : A  → B → B,
        Proper (X.eq ==> eqB ==> eqB) f -> 
        transpose_neqkey B eqB f -> 
        MapsPtes.transpose_neqkey eqB (iter B f).
  Proof.
    intros B eqB eqBeq f H H0.
    red.
    intros k k' e e' a H1.  
    induction e as [|e]; simpl.
    induction e' as [|e'];  simpl.
    apply H0;assumption.
    rewrite <- IHe'.
    apply H0;assumption.
    
    rewrite IHe.
    clear IHe.
    induction e' as [|e'];  simpl in *.
    apply H0;assumption.
    rewrite <- IHe'.
    apply H0;assumption.
  Qed.  


  Lemma fold_morph : 
    ∀ (B : Type) (eqB : B → B → Prop),
      Equivalence eqB
      → (∀ f : A  → B → B,
           Proper (X.eq ==> eqB ==> eqB) f
           → transpose_neqkey _  eqB f
           → (∀ (m1 m2 : t) (i j: B),
                eqB i j ->
                m1 == m2 → eqB (fold _ f m1 i) (fold _ f m2 j))).
  Proof.
    intros B eqB H f H0 H1 m1 m2 i j h H2.
    revert m2 H2.
    unfold fold.
    apply MapsPtes.fold_rec_weak.
    
    - intros m m' a H2 H3 m2 H4.
      apply H3.
      rewrite H2;assumption.

    - intros m2 H2.
      rewrite MapsPtes.fold_Equal with (eqA:=eqB); auto.
      + rewrite MapsPtes.fold_Empty;auto.
        * apply Maps.empty_1.
      + apply iter_proper;assumption.
      + apply iter_transpose_neqkey;assumption.
      + symmetry in H2;eexact H2.

    - intros k e a m H2 H3 m2 H4.
      rewrite MapsPtes.fold_Equal with (eqA:=eqB);auto.
      + rewrite MapsPtes.fold_add.
        assert (Proper (X.eq ==> Logic.eq ==> eqB ==> eqB) (iter B f)).
        apply iter_proper;assumption.
        rewrite <- H3;reflexivity.
        assumption.
        apply iter_proper;assumption.
        apply iter_transpose_neqkey;assumption.
        assumption.
      + apply iter_proper;assumption.
      + apply iter_transpose_neqkey;assumption.
      + symmetry in H4;eexact H4.
  Qed.    


  Add Parametric Morphism (T:Type) (f:_)
      (eqT:T → T → Prop) (H:Equivalence eqT)
      (H2:Proper (X.eq ==> eqT ==> eqT) f )
      (H3:transpose_neqkey _  eqT f) : (fold T f) with signature
      (eq ==> eqT ==> eqT) as fold_morphism.
  Proof.
    intros x y H0 x0 y0 H1.
    eapply (@fold_morph T eqT);auto.
  Qed.

  Lemma remove_all_find:
    forall m e e',
      ~ X.eq e e' ->
      Maps.find e (remove_all e' m) = Maps.find e m.
  Proof.
    intros m e e' H.
    unfold remove_all.
    apply MapsPtes.F.remove_neq_o.
    intro abs.
    symmetry in abs.
    contradiction.
  Qed.
  

  Add Morphism remove_all with signature
      (X.eq ==> eq ==> eq) as remove_all_morph.
  Proof.
    intros x y H x0 y0 H0.
    unfold remove_all.
    rewrite H0.
    rewrite H.
    reflexivity.
  Qed.

  Add Parametric Morphism (T:Type) (f:_)
      (eqT:T → T → Prop) (H:Equivalence eqT)
      (H2:Proper (X.eq ==> eqT ==> eqT) f ): (iter T f) with signature
      (X.eq ==> Logic.eq ==> eqT ==> eqT) as iter_morph.
  Proof.
    intros x y H0 y0 x0 y1 H1.
    induction y0.
    - simpl.
      rewrite H1.
      rewrite H0.
      reflexivity.
    - simpl.
      rewrite H0 at 1.
      rewrite IHy0.
      reflexivity.
  Qed.

  Lemma remove_add':
    forall n A Γ,
      eq
        (remove_all A (Maps.add A n Γ))
        (remove_all A Γ).
  Proof.
    intros n A Γ.
    hnf.
    unfold multiplicity,remove_all.
    intros y.
    destruct (X.eq_dec y A).
    - rewrite e.
      rewrite MapsFact.remove_eq_o;auto.
      rewrite MapsFact.remove_eq_o;auto.
    - rewrite MapsFact.remove_neq_o;auto.
      rewrite MapsFact.remove_neq_o;auto.
      apply MapsFact.add_neq_o.
      auto.
  Qed.

  Lemma remove_add_multiple:
    forall n A Γ,
      eq
        (remove_all A (add_multiple A n Γ))
        (remove_all A Γ).
  Proof.
    unfold add_multiple.
    intros n A Γ.
    destruct (multiplicity A Γ); apply remove_add'.
  Qed.

  Lemma remove_add:
    forall A Γ,
      eq
        (remove_all A (add A Γ))
        (remove_all A Γ).
  Proof.
    unfold add.
    intros A Γ.
    destruct (multiplicity A Γ); apply remove_add'.
  Qed.


  
  Lemma multiplicity_fold :
    ∀ (B : Type) (eqB : B → B → Prop),
      Equivalence eqB ->
      ∀ f : A  ->  B  ->  B,
        Proper (X.eq ==> eqB ==> eqB) f ->
        transpose_neqkey B eqB f ->
        forall (A:_) Γ init n,
          Multiplicity A n Γ ->
          eqB (fold _ f Γ init) (iter _ f A n (fold _ f (remove_all A Γ) init)) .
  Proof.
    intros B eqB H f H0 H1 A Γ init.
    intros n H2.
    rewrite Multiplicity_multiplicity in H2.
    unfold fold,multiplicity in *.
    assert (Maps.Equal Γ (Maps.add A n (Maps.remove A Γ))).
    { unfold Maps.Equal.
      intros y.
      destruct (X.eq_dec y A).
      - rewrite <- e in H2.
        rewrite H2.
        rewrite MapsFact.add_eq_o.
        + reflexivity.
        + symmetry.
          assumption.
      - rewrite MapsFact.add_neq_o.
        + rewrite MapsPtes.F.remove_neq_o.
          * reflexivity.
          * intro abs. symmetry in abs. contradiction.
        +  intro abs. symmetry in abs. contradiction. }
    transitivity  (Maps.fold (iter B f) (Maps.add A n (Maps.remove A Γ)) init).
    - assert (Proper ((X.eq ==> Logic.eq ==> eqB ==> eqB)) (iter B f)).
      { repeat (hnf; intros).
        subst. rewrite H4.
        rewrite H6.
        reflexivity. }
      assert (h:Proper ((Maps.Equal ==> eqB ==> eqB)) (Maps.fold (iter B f))).
      { repeat (hnf; intros).
        eapply MapsPtes.fold_Equal2;auto.
        unfold MapsPtes.transpose_neqkey.
        apply iter_transpose_neqkey;auto. }
      hnf in h.
      unfold respectful in h.
      rewrite (h _ _ H3 init init).
      reflexivity.
      reflexivity.
    - unfold remove_all.
      apply MapsPtes.fold_add.
      + apply H.
      + repeat (hnf; intros).
        subst. rewrite H4.
        rewrite H6.
        reflexivity.
      + unfold MapsPtes.transpose_neqkey.
        intros k k' e e' a H4.
        apply iter_transpose_neqkey;auto.
        * { constructor. (* reversabilité de l'équivalence. *)
            - red.
              intros x.
              reflexivity.
            - red.
              intros x y H5.
              symmetry.
              assumption.
            - red.
              intros x y z H5 H6.
              transitivity y.
              + assumption.
              + assumption. }
        * repeat (hnf; intros).
          apply H0;auto.
        * hnf.
          intros k0 k'0 a0.
          hnf in H1.
          simpl.
          apply H1.
      + apply Maps.remove_1.
        reflexivity.
  Qed.

  Lemma remove_no_mem : forall a ms,
                          ~In a ms
                          -> eq (remove_all a ms) ms .
  Proof.
    intros a ms H.
    unfold In in *.
    unfold remove_all,eq,multiplicity.
    intro y.
    destruct (X.eq_dec a y).
    - rewrite e.
      rewrite MapsFact.remove_eq_o;auto.
      symmetry.
      apply MapsFact.not_find_in_iff.
      rewrite <- e.
      assumption.
    - rewrite MapsFact.remove_neq_o;auto.
  Qed.

  Lemma multiplicity_none_notin: forall a ms, multiplicity a ms = None -> ~ In a ms.
  Proof.
    intros a ms h.
    unfold multiplicity,In in *.
    apply MapsFact.not_find_in_iff.
    assumption.
  Qed.

  (* toto3' *)
  Lemma Add_multiple_neq_o : forall φ ψ n Γ Γ',
                               ~ X.eq φ ψ ->
                               Add_multiple φ n Γ Γ' ->
                               In ψ Γ' ->
                               In ψ Γ.
  Proof.
    intros ψ φ n Γ Γ' H H0 H1.
    apply in_find_iff.
    rewrite <- Add_multiple_add_multiple in H0.
    rewrite <- H0 in H1.
    apply in_find_iff in H1.
    rewrite add_multiple_neq_o in H1;auto.
  Qed.


  Lemma In_dec : ∀ Γ φ, {(φ ∈ Γ)} + {(~ φ ∈ Γ)}.
  Proof.
    intros Γ φ.
    destruct (MapsFact.In_dec Γ φ);auto.
  Qed.

  Lemma empty_in_iff : ∀ x, x ∈ (empty) ↔ False.
  Proof.
    unfold In.
    apply MapsFact.empty_in_iff.
  Qed.

(*
(* toto3 *)
Lemma toto3 : forall A φ ψ (n:A) Γ Γ',
                ¬ X.eq φ  ψ ->
                MapsPtes.Add φ n Γ Γ' ->
                Maps.In ψ Γ' ->
                Maps.In ψ Γ.
Proof.
  intros A ψ φ n Γ Γ' H H0 H1.
  unfold MapsPtes.Add in *.
  rewrite MapsFact.in_find_iff in H1.
  apply MapsFact.in_find_iff.
  intro abs.
  rewrite MapsFact.add_neq_o in H0.
  unfold Maps.find in H0.
  rewrite MapsPtes.F.mem_in_iff in H1.
  rewrite MapsPtes.F.mem_find_b in *.
  rewrite H0 in H1.
  rewrite (MapsFact.add_neq_o ) in H1.
  assumption.
  assumption.
Qed.


Lemma toto3' : forall φ ψ n Γ Γ',
                φ <> ψ ->
                ENV.Add_multiple φ n Γ Γ' ->
                ENV.In ψ Γ' ->
                ENV.In ψ Γ.
Proof.
  intros ψ φ n Γ Γ' H H0 H1.
  rewrite <- ENV.Add_multiple_add_multiple in H0.

  unfold ENV.MapsPtes.Add in *.
  rewrite ENV.MapsPtes.F.mem_in_iff in *.
  rewrite ENV.MapsPtes.F.mem_find_b in *.
  rewrite H0 in H1.
  rewrite (ENV.MapsFact.add_neq_o ) in H1.
  assumption.
  assumption.
Qed.


Lemma toto : forall φ n (Γ Γ':  ENV.Maps'.t ℕ),
               ENV.MapsPtes.Add φ n Γ Γ'
               -> ENV.Maps'.In (elt:=ℕ) φ Γ'.
Proof.
  intros φ n Γ Γ' H0.
  unfold ENV.MapsPtes.Add in *.
  specialize (H0 φ).
  rewrite ENV.MapsPtes.F.mem_in_iff in *.
  rewrite ENV.MapsPtes.F.mem_find_b in *.
  rewrite H0.
  rewrite ENV.MapsFact.add_eq_o;auto.
Qed.

Lemma toto2 : forall φ φ' n (Γ Γ':  ENV.Maps'.t ℕ),
               ENV.Maps'.In (elt:=ℕ) φ Γ
               -> ENV.MapsPtes.Add φ' n Γ Γ'
               -> ENV.Maps'.In (elt:=ℕ) φ Γ'.
Proof.
  intros φ φ' n Γ Γ' H H0.
  unfold ENV.MapsPtes.Add in *.
  specialize (H0 φ).
  rewrite ENV.MapsPtes.F.mem_in_iff in *.
  rewrite ENV.MapsPtes.F.mem_find_b in *.
  rewrite H0.
  destruct (formule_eq_dec φ φ').
  - subst.
    rewrite ENV.MapsFact.add_eq_o;auto.
  - rewrite ENV.MapsFact.add_neq_o;auto.
Qed.

Hint Resolve toto2 toto.

Lemma toto2' : forall φ φ' n (Γ Γ':  ENV.t),
               ENV.In φ Γ
               -> ENV.add_multiple φ' n Γ = Γ'
               -> ENV.In φ Γ'.
Proof.
  intros φ φ' n Γ Γ' H H0.
  unfold ENV.add_multiple in *.
  unfold ENV.In in *.
  destruct (ENV.Maps'.find (elt:=ℕ) φ' Γ);subst.
  - rewrite ENV.MapsFact.add_in_iff.
    destruct (formule_eq_dec φ φ');auto.
  - rewrite ENV.MapsFact.add_in_iff.
    destruct (formule_eq_dec φ φ');auto.
Qed.

Lemma toto2_add' : forall φ φ' (Γ Γ':  ENV.t),
               ENV.In φ Γ
               -> ENV.add φ' Γ = Γ'
               -> ENV.In φ Γ'.
Proof.
  intros φ φ' Γ Γ' H H0.
  rewrite ENV.add_add_multiple in *.
  eapply toto2';eauto.
Qed.



Lemma toto2' : forall φ φ' n (Γ Γ':  ENV.Maps'.t ℕ),
               ENV.In φ Γ
               -> ENV.MapsPtes.Add φ' n Γ Γ'
               -> ENV.In φ Γ'.
Proof.
  intros φ φ' n Γ Γ' H H0.
  eapply toto2;eauto.
Qed.

Hint Resolve toto2'.


Lemma empty_unique :
  forall Γ Γ': env,
    ENV.Maps'.Empty Γ ->
    ENV.Maps'.Empty Γ' ->
    ENV.Maps'.Equal Γ Γ'.
Proof.
  intros Γ Γ' H H0.
  unfold ENV.Maps'.Equal.
  intros y.
  rewrite ENV.Empty_not_find.
  - rewrite ENV.Empty_not_find.
    + reflexivity.
    + assumption.
  - assumption.
Qed.
 *)

  Lemma singleton_eq: forall a b, eq ([a]) ([b]) -> X.eq a b.
  Proof.
    intros a b heq.
    destruct (mem_destruct_iff a b empty) as [hdisj hmem].
    destruct hdisj as [h|h].
    { rewrite <- heq.
      apply mem_in_iff.
      apply in_add_eq.
      reflexivity. }
    - assumption.
    - exfalso.
      rewrite empty_no_mem in h.
      inversion h.
  Qed.

  Lemma dec_singleton: forall φ φ' B, φ :: B == [φ'] -> B==empty /\ X.eq φ φ'.
  Proof.
    intros φ φ' B.
    revert φ φ'.
    induction B using multiset_ind;intros.
    - rewrite <- H in *|-*.
      now apply IHB1.
    - split.
      + reflexivity.
      + now apply singleton_eq.
    - exfalso.
      apply add_singleton_abs with (1:=H).
  Qed.

  Lemma empty_add: forall x Γ, ~(∅ == x::Γ).
  Proof.
    intros x Γ.
    intro abs.
    specialize (empty_in_iff x ) as h.
    rewrite abs in h.
    apply h.
    apply in_add_eq;auto.
  Qed.

  Lemma union_assoc: forall Γ Γ' Γ'', Γ ∪ (Γ' ∪ Γ'') == (Γ ∪ Γ') ∪ Γ''.
  Proof.
    intros Γ.
    induction Γ using multiset_ind;intros.
    - rewrite <- H.
      apply IHΓ1.
    - rewrite union_empty_left.
      rewrite union_empty_left.
      reflexivity.
    - rewrite union_rec_left.
      rewrite union_rec_left.
      rewrite IHΓ.
      rewrite union_rec_left.
      reflexivity.
  Qed.

  Lemma union_union_decomp: forall Γ Γ₁ Δ₁,
      Γ₁ ∪ Δ₁ == Γ ->
      forall Γ₂ Δ₂,
        Γ == Γ₂ ∪ Δ₂ ->
        exists Γ₁₁ Γ₁₂ Δ₁₁ Δ₁₂,
          Γ₁ == Γ₁₁ ∪ Δ₁₁ /\
            Δ₁ == Γ₁₂ ∪ Δ₁₂ /\
            Γ₂ == Γ₁₁ ∪ Γ₁₂ /\
            Δ₂ == Δ₁₁ ∪ Δ₁₂.
  Proof.
    intros Γ.
    induction Γ using multiset_ind;intros ? ? hΓ2 ? ? hΓ2'.
    - rewrite <- H in hΓ2.
      specialize IHΓ1 with (1:=hΓ2).
      rewrite <- H in hΓ2'.
      specialize IHΓ1 with (1:=hΓ2').
      assumption.
    - apply union_empty_decompose in hΓ2.
      symmetry in hΓ2'.
      apply union_empty_decompose in hΓ2'.
      destruct hΓ2.
      destruct  hΓ2'.
      setoid_rewrite H.
      setoid_rewrite H0.
      setoid_rewrite H1.
      setoid_rewrite H2.
      exists ∅,∅,∅,∅.
      repeat split;symmetry; apply union_empty_right.
    - apply union_decompose in hΓ2.
      symmetry in hΓ2'.
      apply union_decompose in hΓ2'.
      destruct hΓ2 as [[ Δ' [hΓ₁ hΓ ] ] | [ Δ' [hΔ₁ hΓ ] ] ];
        destruct hΓ2' as [[ Ω' [hΓ₂ h'Γ ] ] | [ Ω' [hΔ₂ h'Γ ] ] ].
      + specialize IHΓ with (1:=hΓ).
        symmetry in h'Γ.
        specialize IHΓ with (1:=h'Γ).
        decompose [ex and] IHΓ.
        setoid_rewrite H0.
        setoid_rewrite H3.
        setoid_rewrite hΓ₁.
        setoid_rewrite hΓ₂.
        setoid_rewrite H.
        setoid_rewrite H1.
        exists (x::x0).
        exists x1.
        exists x2.
        exists x3.
        repeat split;auto;try now rewrite union_rec_left.
      + specialize IHΓ with (1:=hΓ).
        symmetry in h'Γ.
        specialize IHΓ with (1:=h'Γ).
        decompose [ex and] IHΓ.
        setoid_rewrite H0.
        setoid_rewrite H3.
        setoid_rewrite hΓ₁.
        setoid_rewrite hΔ₂.
        setoid_rewrite H1.
        setoid_rewrite H.
        exists x2.
        exists x3.
        exists (x::x0).
        exists x1.
        repeat split;auto;try now rewrite union_rec_left.
        * rewrite <- union_rec_left.
          rewrite union_sym.
          reflexivity.
        * now rewrite union_sym.
      + specialize IHΓ with (1:=hΓ).
        symmetry in h'Γ.
        specialize IHΓ with (1:=h'Γ).
        decompose [ex and] IHΓ.
        setoid_rewrite H0.
        setoid_rewrite H3.
        setoid_rewrite hΓ₂.
        setoid_rewrite hΔ₁.
        setoid_rewrite H1.
        setoid_rewrite H.
        exists x1.
        exists (x::x0).
        exists x3.
        exists x2.
        repeat split;auto;try now rewrite union_rec_left.
        * rewrite <- union_rec_left.
          rewrite union_sym.
          reflexivity.
        * now rewrite union_sym.
      + specialize IHΓ with (1:=hΓ).
        symmetry in h'Γ.
        specialize IHΓ with (1:=h'Γ).
        decompose [ex and] IHΓ.
        setoid_rewrite H0.
        setoid_rewrite H3.
        setoid_rewrite hΔ₂.
        setoid_rewrite hΔ₁.
        setoid_rewrite H1.
        setoid_rewrite H.
        exists x3.
        exists x2.
        exists x1.
        exists (x::x0).
        repeat split;auto;try now rewrite union_rec_left.
        * now rewrite union_sym.
        * rewrite <- union_rec_left.
          rewrite union_sym.
          reflexivity.
        * now rewrite union_sym.
        * rewrite <- union_rec_left.
          rewrite union_sym.
          reflexivity.
  Qed.

(* Faux. le est une permutation seulement dans le cas général, car rien ne garantit que l'ordre est préservé après u remove_all.
Lemma remove_all_elements:
  forall Γ e n l,
  rev (Maps.elements (elt:=ℕ) Γ) = ((e, n) :: l)%list -> 
  multiplicity e Γ = Some n -> 
  l = rev (Maps.elements (elt:=ℕ) (remove_all e Γ)).
Proof.
  
Qed.
*)

End PreMake.

Module MakeAVL(X:OrderedType )<:S(X).
  Module Maps' := FMapAVL.Make(X).
  Include PreMake(X)(Maps').

  Lemma Add_In_neq : forall A φ ψ (n:A) Γ Γ',
                       ¬X.eq φ ψ ->
                       MapsPtes.Add φ n Γ Γ' ->
                       Maps'.In (elt:=A) ψ Γ' ->
                       Maps'.In (elt:=A) ψ Γ.
  Proof.
    intros A ψ φ n Γ Γ' H H0 H1.
    unfold MapsPtes.Add in *.
    rewrite MapsPtes.F.mem_in_iff in *.
    rewrite MapsPtes.F.mem_find_b in *.
    rewrite H0 in H1.
    rewrite (MapsFact.add_neq_o ) in H1.
    assumption.
    assumption.
  Qed.
(*
  Lemma singleton_eq : forall φ Γ, eq Γ (add φ empty) -> exists φ', (X.eq φ φ' /\ Γ=add φ' empty).
  Proof.
    intros φ Γ H.
    unfold eq,add in H.
    rewrite MapsFact.empty_o in H.
    induction Γ.
    destruct this.
    unfold Maps'.Equal in *.
    absurd (Maps'.find (elt:=nat) φ {| Maps'.this := Maps'.Raw.Leaf nat; Maps'.is_bst := is_bst |}<>None).
    vm_compute.
    auto.
    rewrite H.
    vm_compute.
    case (X.compare φ φ).
    clear;intros abs _.
    elim (X.lt_not_eq abs).
    apply X.eq_refl.
    discriminate.
    intros abs _.
    elim (X.lt_not_eq abs).
    apply X.eq_refl.

    destruct this1.
{
    destruct this2.
    destruct n.
    exists k.
    split.
    vm_compute in H.
    generalize (H φ).
    case (X.compare φ φ).
    clear;intros abs _.
    elim (X.lt_not_eq abs).
    apply X.eq_refl.
    case (X.compare φ k).
    discriminate.
    tauto.
    discriminate.
    clear;intros abs _.
    elim (X.lt_not_eq abs).
    apply X.eq_refl.
    vm_compute in H|-*.
    inversion is_bst.
    Qed.
 *)

End MakeAVL.

Module MakeList(X:DecidableType )<:S(X).
  Module Maps' := FMapWeakList.Make(X).
  Include PreMake(X)(Maps').
End MakeList.

(*
Module MakeRawList(X:OrderedType)<:S(X).
  Local Notation A := X.t.
  Definition t := list A.

  Definition empty : t := nil.

  Definition is_empty (l : t) := match l with nil => true | _ => false end.

  Definition add := cons (A:=A).

  Function mem (e:A) (ms:t) {struct ms} : bool := 
    match ms with 
      | nil => false 
      | e'::ms' => 
        match X.compare e e' with 
          | EQ _ => true 
          | _ => mem e ms'
        end
    end.
  
  Inductive eq' : t -> t -> Prop := 
  | Eq_nil : eq' nil nil 
  | Eq_cons : forall e1 e2 ms1 ms2 ms2', X.eq e1 e2 -> eq' ms1 (ms2++ms2') -> eq' (e1::ms1) (ms2++e2::ms2').

  Definition eq := eq'.

  Function find_decomp (e:A) (ms:t) (acc:t) {struct ms} : option (A*t*t) := 
    match ms with 
      | nil => None 
      | e'::ms' => 
        match X.compare e e' with 
          | EQ _ => Some(e',List.rev acc,ms')
          | _ => find_decomp e ms' (e'::acc)
        end
    end.

  Lemma rev_cons : forall A l1 (e:A) l2, rev (e::l1)++l2 = rev l1 ++ e :: l2.
  Proof.
    destruct l1 as [|e1 l1].

    intros e l2.
    reflexivity.

    intros e l2.
    simpl.
    repeat rewrite <- app_assoc.
    simpl. reflexivity.
  Qed.

  Lemma find_decomp_concat : forall e e' ms m m' acc, find_decomp e ms acc = Some(e',m,m') -> 
    (List.rev acc)++ms = m++e'::m'.
  Proof.
    intros e e' ms m m' acc.
    revert e' m m'.
    functional induction (find_decomp e ms acc).

    intros e' m m' H;discriminate H.

    intros e'0 m m' H.
    injection H;clear H;intros;subst.
    reflexivity.

    intros e'0 m m' H.
    rewrite <- rev_cons.
    apply IHo;assumption.
  Qed.
    
  Lemma find_decomp_eq : forall e e' ms m m' acc, find_decomp e ms acc = Some(e',m,m') -> 
    X.eq e e'.
  Proof.
    intros e e' ms m m' acc.
    revert e' m m'.
    functional induction (find_decomp e ms acc).

    intros e' m m' H;discriminate H.

    intros e'0 m m' H.
    injection H;clear H;intros;subst.
    assumption.

    intros e'0 m m' H.
    eauto.     
  Qed.


  Function eq_bool (ms1 ms2:t) {struct ms1} : bool := 
    match ms1,ms2 with
      | nil,nil => true
      | e1::ms1,e2::ms2 =>
        match find_decomp e1 (e2::ms2) nil with 
          | None => false 
          | Some (_,ms2,ms2') => eq_bool ms1 (ms2++ms2')
        end
      | _,_ => false
    end.
  
  Lemma eq_bool_correct : forall m1 m2, eq_bool m1 m2 = true -> eq m1 m2.
  Proof.
    intros m1 m2;functional induction (eq_bool m1 m2);intros Heqb.

    constructor.

    discriminate.

    generalize (find_decomp_concat _ _ _ _ _ _ e3);simpl;intros.
    generalize (find_decomp_eq _ _ _ _ _ _ e3);simpl;intros.
    rewrite H in *.
    constructor 2;auto.

    discriminate.
  Qed.

  Lemma eq_refl : forall ms, eq ms ms.
  Proof.
    induction ms as [|e ms IH].
    
    constructor. 

    change (e :: ms) with (nil ++ e :: ms) at 2. 
    constructor .
    apply X.eq_refl.
    simpl;assumption.
  Qed.
  Lemma eq_sym : forall ms ms', eq ms ms' -> eq ms' ms.
  Admitted.     
    
  Lemma eq_trans : forall ms1 ms2 ms3, eq ms1 ms2 -> eq ms2 ms3 -> eq ms1 ms3.
  Admitted.
    

  Lemma add_morph_eq : forall a a', X.eq a a' -> forall ms ms',  eq ms ms' -> eq (add a ms) (add a' ms'). 
  Proof.
    intros a a' H ms ms' H0.
    change (add a' ms') with (nil ++ a' :: ms');constructor 2;simpl;auto.
  Qed.

  Definition union := app (A:=A). 

  Lemma union_morph_eq : forall a a', eq a a' -> forall ms ms',  eq ms ms' -> eq (union a ms) (union a' ms'). 
  Proof.
    unfold union.
    intros a a' H.
    induction H.

    simpl;tauto.

    intros ms ms' H1.
    simpl.
    rewrite <- app_assoc.
    simpl.
    constructor 2.
    assumption.
    rewrite app_assoc.
    auto.
  Qed.


  Lemma is_empty_empty : is_empty empty = true.
  Proof.
    vm_cast_no_check (refl_equal true).
  Qed.
  Module XFacts := OrderedTypeFacts(X).

  Lemma is_empty_no_mem : forall ms, is_empty ms = true <-> (forall a, mem a ms = false). 
  Proof.
    
    intros ms.
    split.

    destruct ms;simpl.
    tauto.
    discriminate.

    destruct ms;simpl.
    reflexivity.
    intros.
    assert (U:=H t0);clear H.
    destruct (X.compare t0 t0). 
    elim (XFacts.lt_antirefl l).
    discriminate.
    elim (XFacts.lt_antirefl l).
  Qed.
   
  Lemma add_is_not_empty : forall a ms, is_empty (add a ms) = false.
  Proof.
    intros a ms.
    simpl;reflexivity.
  Qed.

  Lemma add_is_mem : forall a ms, mem a (add a ms) = true.
  Proof.
    intros a ms.
    simpl.
    destruct (X.compare a a).
    elim (XFacts.lt_antirefl l).
    reflexivity.
    elim (XFacts.lt_antirefl l).
  Qed.

  Lemma add_comm : forall a b ms, eq (add a (add b ms)) (add b (add a ms)).
  Proof.
    unfold add.
    intros a b ms.
    change (b::a::ms) with ((b::nil)++a::ms);constructor 2.
    apply X.eq_refl.
    apply eq_refl.
  Qed.

  (* Parameter remove_mem : forall a ms, mem a ms = true -> exists ms', remove a ms = Some ms'. *)
  (* Parameter remove_not_mem : forall a ms, mem a ms = false -> remove a ms = None. *)
 
  Lemma mem_add_comm : forall a b ms, mem a ms = true -> mem a (add b ms) = true.
  Proof.
    intros a b ms;revert b.
    functional induction (mem a ms);try discriminate.
    
    intros b _.
    simpl.
    destruct (XFacts.elim_compare_eq _x).
    rewrite H.
    destruct (X.compare a b);reflexivity.


    intros b H.
    
    simpl in *.
    destruct (X.compare a e');try tauto;    auto.
  Qed.

  Lemma union_empty_left : forall ms, eq (union empty ms) ms.
  Proof.
    intros.
    vm_compute. apply eq_refl.
  Qed.

  Lemma union_empty_right : forall ms, eq (union ms empty) ms.
  Proof.
    intros ms.
    unfold empty,union.

    induction ms as [| e ms].
    constructor 1.
    simpl.
    rewrite app_nil_r.
    apply eq_refl.
  Qed.

  Lemma union_rec_left : forall a ms ms', eq (union (add a ms) ms') (add a (union ms ms')).
  Proof.
  Admitted.
  Lemma union_rec_right : forall a ms ms', eq (union ms (add a ms')) (add a (union ms ms')).
  Admitted.

  Lemma mem_morph_eq :
    forall (φ : A) (Γ Γ' : t), eq Γ Γ' -> mem φ Γ = mem φ Γ'.
  Admitted.
End MakeRawList.
 *)
