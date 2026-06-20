(** remove printing -> *)
(** remove printing forall *)
(** remove printing exists *)
(** remove printing ~ *)
(** remove printing => *)
(** printing -> $\longrightarrow$ #––># *)

(** Ce module implante quelques utilité techniques sur les
    environnements de preuve. Il n'est pas utile au cours, vous ne
    devez pas le lire. *)


From Stdlib Require Import Utf8_core Morphisms Setoid OrdersEx.

Require Import GenEnv.GenericEnv GenEnv.GenericEnvList.
(* Les variables sont représentées par les entiers naturels. *)
Module ENV := GenericEnvironmentAsList(Nat_as_DT). (* Structures.OrderedTypeEx.Nat_as_OT *)
Export ENV.
Export Core.
Open Scope gen_env_scope.



Definition pop_forget {A} (s:gen_env A): option (gen_env A) :=
  match pop s with
    | Some (_,x) => Some x
    | None => None
  end.

Fixpoint pop_forgetl {A}  n (s:(gen_env A)): (option (gen_env A)) :=
  match n with
    | 0 => Some s
    | S n' =>  match pop s with
                 | Some (_,x) => pop_forgetl n' x
                 | None => None
               end
  end.

Fixpoint pushl {A} (lnme:list nat) (lval:list A) (s: (gen_env A)): option (gen_env A) :=
  match lnme with
    | nil => match lval with
               | nil => Some s
               | _ => None
             end
    |  cons nme lnme' =>
       match lval with
         | nil => None
         | cons v lval' =>
           match pushl lnme' lval' s with
             | None => None
             | Some s' => Some (push nme v s')
           end
       end
  end.


Lemma refl : ∀ {A},∀ x : @gen_env A, Ext.eq x x.
Proof.
  intros A x.
  apply Ext.eq_refl;trivial.
Qed.


Lemma eq_sym : ∀ {A} x y, @Ext.eq A x y → Ext.eq y x.
Proof.
  intros A x y H.
  apply Ext.eq_sym ;trivial.
Qed.

Lemma eq_trans : ∀ {A} x y z, @Ext.eq A x y → Ext.eq y z → Ext.eq x z.
Proof.
  intros A x y z H H0.
  apply Ext.eq_trans with y;auto.
Qed.

Add Parametric Relation (A:Type) : (gen_env A) (@Ext.eq A)
               reflexivity proved by refl
               symmetry proved by eq_sym
               transitivity proved by eq_trans as eq_rel.



(* begin hide *)
Add Parametric Morphism (A:Type):
  (@update_one A) with signature (@Ext.eq _) ==> (eq) ==> (eq) ==> (@Ext.eq _)
                    as update_one_morph.
Proof.
  intros x y H y0 y1.
  rewrite <- update_update_one.
  rewrite <- update_update_one.
  apply Ext.eq_update.
  assumption.
Qed.

(* Manque un lemme *)
(*
Add Parametric Morphism (A:Type):
  (@update A) with signature (@Ext.eq _) ==> (@Ext.eq _) ==> (@Ext.eq _)
                as update_morph.
Proof.
  intros x y H x0 y0 H0.
  transitivity (y ::= x0).
  - apply Ext.eq_update.
    assumption.
  - 
Qed.
*)

(* end hide *)

(* Notation " E '[' x ']' '=' e " := (@Ext.binds _ x e E) (at level 65) :Prog_scope. *)
(* Notation " x '-:' e 'IN' E" := (@Ext.binds _ x e E) (at level 66): Prog_scope. *)
(* Notation " E '[' x '←' v ']'" := (update_one E x v) (at level 67): Prog_scope. *)


(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-load-path: ("./Generic_Env_v0.3") ***
*** End: ***
*)
