(* O Pons 2012 *)

(* 
 definir les formules de la logique propositionelle
*)
Inductive prop:Set :=
   mFalse :prop 
  |mVar : nat ->prop
  |mNot : prop  ->prop
  |mImp:  prop ->prop ->prop
  |mOr : prop ->prop ->prop
  |mEt : prop->prop->prop.
 

(* definir A/\B=> B *)
Definition AetBImpB := (mImp (mEt (mVar O) (mVar (S O)))(mVar (S 0))).


(* neg sur les booleen deja definie negb dans Init/DataType.v
Fixpoint neg (b:bool) :=
match b with 
false =>true
 |true =>false
 end.
 *)
 
(* evaluation  *)
Function eval (p:prop)(valuation:(nat->bool)) {struct p}: bool :=
   match p with
   mFalse =>false
   |mVar n => (valuation n)
   |mNot p0 => negb (eval p0 valuation)
   |mImp p0 p1 =>match (eval p0 valuation) with 
                   false =>true
                   |true =>  (eval p1 valuation) 
                   end
   |mOr p0 p1 => match (eval p0 valuation) with
                   true =>true
                   |false =>(eval p1 valuation)
                   end
   |mEt p0 p1 => match (eval p0 valuation) with
                   true =>(eval p1 valuation)
                    |false =>false
                    end                 
    end.
Require Import List.

Function vars    (p:prop)( i:list nat) :  list nat :=
  match p with
   mFalse =>i
   |mVar n =>n::i
   |mNot p0 =>(vars p0 i)
   |mImp p0 p1 =>(vars p0 i)++(vars p1 i)
   |mOr p0 p1 =>(vars p0 i)++ (vars p1 i)
   |mEt p0 p1 =>  (vars p0 i)++(vars p1 i)             
    end.
Check head.
Inductive varsi : prop ->list nat->Prop :=
    VmFalse : (varsi mFalse nil)
   |VmVar : forall i n,  (i=n::nil)->(varsi (mVar n) i)
   |VmNot : forall p0 i,(varsi p0 i) -> (varsi (mNot p0) i) 
   |VmImp :forall p0 p1 i j,(varsi p0 i) -> (varsi p1 j )->(varsi (mImp p0 p1) (i++j)) 
   |VmOr :forall p0 p1 i j,(varsi p0 i) -> (varsi p1 j )->(varsi (mOr p0 p1)(i++j)) 
   |VmEt :forall p0 p1 i j,(varsi p0 i) -> (varsi p1 j )->(varsi (mEt p0 p1) (i++j ))     
.

Lemma varsiVars : forall p, (varsi p (vars p nil)).
induction p;simpl;constructor;trivial.
Qed.

Definition Valuation := list (nat * bool).
Require Arith.

Function getValue (v:Valuation)(x:nat) : option bool :=
  match v with
    | nil => None
    | (y, c) :: tl => if (NPeano.Nat.eq_dec x y) then Some c else getValue  tl x
  end.




Require Import List.


(* vovabulaire *)
Definition tautologie (p:prop) :=forall v:nat->bool, (eval p v)=true. 

Definition satisfiable (p:prop) :=exists v:nat->bool, (eval p v)=true. 


Definition insatifiable (p:prop) :=forall v:nat->bool, (eval p v)=false. 

Definition equivalent (p1:prop) (p2:prop) :=
  forall v:nat->bool, (eval p1 v)=(eval p2 v). 


(* 
on note phi(p,v) la formule e_1(x_1)/\.../\e_n(x_n) 
ou les x_i sont les variable de p et ou e_i(X_i) = X si v(x)=true
et e_i(x_i)= ~X si v(x)=false
*)
Function phi    (p:prop)(valuation:nat->bool) : prop :=
  match p with
   mFalse =>(mNot mFalse)
   |mVar n =>if (valuation n) then (mVar n) else (mNot (mVar n)) 
   |mNot p0 =>(phi p0 valuation)
   |mImp p0 p1 =>(mEt (phi p0 valuation ) (phi p1 valuation))
   |mOr p0 p1 =>(mEt (phi p0 valuation ) (phi p1 valuation))
   |mEt p0 p1 =>(mEt (phi p0 valuation ) (phi p1 valuation))
    end.




(* 
   des ensembles de formules codes ici par des listes
   faire mieux avec FSet ...
*)
Definition env := (list prop).


(* defintion inductive d'une preuve en deduction naturelle *)
Inductive pfN :  env ->env -> Prop :=
  AxN : forall gamma, forall p:prop, (In  p gamma  ) ->(pf  gamma p)
 |Impe :forall gamma,forall p0:prop, forall p1, (pf  gamma (mImp p0 p1) )->(pf gamma p0) ->(pf  gamma p1)
 |Impi :forall gamma,forall p0:prop, forall p1, (pf  (cons p0 gamma) p1) ->(pf  gamma (mImp p0 p1))
 |andi :forall gamma,forall p0:prop, forall p1, (pf  gamma p0) ->(pf  gamma p1) ->(pf  gamma (mEt p0 p1)) 
 |ande1 :forall gamma,forall p0:prop, forall p1, (pf  gamma (mEt p0 p1)) ->(pf  gamma p0)
 |ande2 :forall gamma,forall p0:prop, forall p1, (pf  gamma (mEt p0 p1)) ->(pf  gamma p1)
 |noti : forall gamma,forall p0:prop, (pf  (cons p0 gamma) mFalse) ->(pf  gamma (mNot p0) )
 |note :forall gamma,forall p0:prop, forall p1, (pf  gamma p0 ) ->(pf  gamma (mNot p0))->(pf  gamma p1)
 |ore:forall gamma,forall p0:prop, forall p1, forall p2, (pf  gamma (mOr p0 p1)) ->
                (pf   (cons p0 gamma) p2) -> (pf   (cons p1 gamma) p2) ->(pf  gamma p2)
  |ori1 :forall gamma,forall p0:prop, forall p1, (pf  gamma p0)->(pf  gamma (mOr p0 p1))
|ori2 :forall gamma,forall p0:prop, forall p1, (pf  gamma p1)->(pf  gamma (mOr p0 p1))
|fale :forall gamma,forall p0:prop,(pf  (cons (mNot p0) gamma) mFalse)->(pf  gamma p0 ).




Definition Uphi :forall F:prop, 

Lemma UphiProuvable : forall F:prop,( pf nil  (phi F d))).
induction F;simpl;intros.
   exists (fun O =>true).
   apply noti.
   apply Ax.
   simpl.
   left;trivial.

   elim n.
     exists (fun O =>true).

Lemma trueNotFalse : forall p:prop, forall v:nat->bool, (eval p v)=true -> ~  (eval p v)=false.
intros.
unfold not.
rewrite H.
intros H1.
info inversion H1.
Qed.

(*Preuve de coherence *)
Lemma soundness :  forall gamma, forall p:prop, (pf  gamma p) -> forall v:nat->bool, (forall f, (In f gamma-> (eval f v)=true)) -> (eval  p v)=true.
intros.
induction H. (*induction sur la structure de la preuve *)
(*Ax*)
intros.
apply H0.
assumption.

(*impe *)
intros.


specialize (IHpf1 H0).
 inversion IHpf1.



rewrite (IHpf2 H0).
trivial.




(* impi *)

simpl.
case_eq (eval p0 v).
2:trivial.
intro.
apply IHpf.
intro.
simpl.
intro h.
destruct h.
subst.
assumption.
apply H0.
assumption.

(*eti*)
simpl.
case_eq (eval p0 v).
intros.
apply IHpf2.
assumption.
intros.
rewrite<- H2.
apply IHpf1.
assumption.


(*ete1 *)
simpl in IHpf.
case_eq (eval p0 v);intros.
trivial.
rewrite H1 in IHpf.
apply IHpf.
assumption.

(*ete2 *)
simpl in IHpf.
case_eq (eval p0 v);intros;
rewrite H1 in IHpf.
apply IHpf.
assumption.
absurd (false = true).
discriminate.
apply IHpf.
assumption.

(* noti *)
simpl.
unfold negb.
case_eq (eval p0 v);intros.
2:trivial.
simpl in IHpf.
apply IHpf.

intro.
intro h;destruct h.
subst.
assumption.
apply H0.
assumption.


(* note *)
case_eq (eval p0 v);intros.
simpl in IHpf2.
rewrite H2 in *.
simpl in *.
absurd (false = true).
discriminate.
apply IHpf2.
assumption.

simpl in IHpf2.
rewrite H2 in *.
absurd (false = true).
discriminate.
apply IHpf1.
assumption.


(* ore *)
case_eq (eval p0 v).
intros.
apply IHpf2.
intro.
intro h.
destruct h.
subst.
assumption.
apply H0.
assumption.

intros.

case_eq (eval p1 v).

intros.
apply IHpf3.
intro.
intro h.
destruct h.
subst.
assumption.
apply H0.
assumption.

intros.
simpl in IHpf1.
rewrite H3 in IHpf1.


rewrite H4 in IHpf1.

absurd (false = true).
discriminate.
apply IHpf1; assumption.


(* ori1 *)
simpl.
case_eq (eval p0 v).
trivial.
intros.
absurd (true =false).
discriminate.
rewrite H1 in IHpf.
symmetry.
apply IHpf.
assumption.


(* ori2 *)
simpl.
case_eq (eval p0 v);case_eq (eval p1 v);trivial.
intros.
absurd (true =false).
discriminate.
rewrite H1 in IHpf.
symmetry.
apply IHpf.
assumption.

(* False *)
case_eq (eval p0 v).
trivial.
simpl in IHpf.
intros.
apply IHpf.


intro.
intro h;destruct h.
subst.
simpl.
rewrite H1.
simpl;trivial.
apply H0.

assumption.

Qed.



Fixpoint mesure (p :prop){struct p}:nat :=
   match p with
     mFalse =>0
    |mVar _ =>1
    |mNot p1 =>mesure(p1)+1
    |mImp p1 p2 =>mesure(p1)+mesure(p2)+1
    |mOr p1 p2 =>mesure(p1)+mesure(p2)+2
    |mEt p1 p2 =>mesure(p1)+mesure(p2)+1
     end.
Fixpoint gammaMesure (gamma :env):nat :=
    match gamma with
       nil =>0
       |cons hd1 tl1=>mesure(hd1)+gammaMesure(tl1)
    end.

Require Import Wf_nat.
Print lt_wf.
Print well_founded.
Print ltof.
(* definition de la relation d'ordre sur les env *)
Definition gammaLt (n m:env) := (gammaMesure n) < (gammaMesure m).

(* on montre qu'elle est bien fondee*)
Lemma gammaLt_wf : well_founded gammaLt.
apply well_founded_ltof.
Qed.
Print In_dec.
Print in_dec.
Scheme Equality for prop.
(*
Lemma prop_eq_dec : forall x y : prop, { eq x y } + { ~ eq x y }.
intros.
case x;case y;intros;
repeat progress (apply right;discriminate).
apply left ;trivial.
 Scheme Equality for nat.
case (nat_eq_dec n n0).
intro eqN;left;rewrite eqN;trivial.
*)
Definition models (gamma:env) (p:prop):=
 (forall v:nat->bool, 
   (forall f, In f gamma-> (eval f v)=true)->
   (eval  p v)=true).


Definition P1 :forall n,forall gamma, forall A, 
     (gammaMesure (cons A gamma))=n->
    (models gamma A)->(pf gamma A).

Lemma compleness : forall gamma, forall p,
 (models gamma p)->(pf  gamma p).
Print well_founded_induction.
apply (well_founded_induction  gammaLt_wf).
2:exact nil. (* comprendre pourquoi il y a ce second but !*)

intros Sgamma HRec gamma p.
 Check (in_dec prop_eq_dec).
case p. (* 6 cas *)
(* false *)
unfold models;simpl.
intros.

(* pour utiliser In_dec on doit montrer la decidabilite de l'egalite sur prop *)
Focus 3.
(* cas mFalse *)
simpl in H.
constructor 1.
absurd(true=false).
discriminate.
symmetry.
apply (H (fun _ =>true)).
intros.


(* cas mVar *)
intros.
simpl in H.
absurd (true=false).
discriminate.
symmetry.
apply (H (fun _ =>false)).


intros.
absurd  (eval mFalse v = true).
Check note.
apply (note gamma mFal.
functional inversion H.
(* Ax *)
apply Ax.




