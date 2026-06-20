Inductive spec_args : Type :=
  ConsQuantif: spec_args -> spec_args
| ConsEvar: spec_args -> spec_args
| ConsIgnore: spec_args -> spec_args
| ConsSubGoal: spec_args -> spec_args
| SubGoalEnd: spec_args.

(* List storing heterogenous terms, for storing (tele(scopes). A
   simple product could also be used. *)
Inductive Depl :=
| DNil: Depl
| DCons: forall (A:Type) (x:A), Depl -> Depl.

Declare Scope specialize_scope.
Delimit Scope specialize_scope with spec.
Local Open Scope specialize_scope.


(* builds the application of c to each element of l (in reversed
   order). apply t [t1;t2;t3] => (t t3 t2 t1) *)
Ltac list_apply c l :=
  match l with
    DNil => c
  | DCons _ ?x ?l' =>
      let inside := list_apply c l' in
      let res := constr:(ltac:(exact (inside x))) in
      res
  end.

(* - We start from a goal evar EV with no typing constraint.

    h: forall x y z, P x -> ...
    ========================
    ?EV

    subgoal 2
    h: forall x y z, P x -> ...
    ========================
    old goal
    

  - We refine it to have the same products at head than h, until we
    reach the aimed hypothesis

    h: P x -> ...
    x: ...   y: ...   z: ...
    ========================
    ?EV

  - then we do 2 things
    - create a goal USERGOAL for this hyp
    - conclude EV (and fix its type) by applying h to USERGOAL

    subgoal 1
    x: ...   y: ...   z: ...
    ==========================
    P x

    subgoal 2:
    h: forall x y z, P x -> ...
    hEV: forall x y z, ...
    ==========================
    old goal

   Refines a non specified goal (an evar) to prove the specialized
   version of h. The idea is to use (fun x y z => (?ev x y z)) as the
   argument being instnaciated, where ?ev will be the new goal

 larg is the specidication of what to do with each arg, larg2 is the
   accumulator *)
Ltac refine_hd h largs largs2 :=
  match largs with
  | SubGoalEnd => match type of h with
                  | (forall x:?t, _) =>
                      let h' := fresh h in
                      (* create the user subgoal *)
                      assert(t) as h'
                      ;[ clear h
                       | exact (h h')
                         (*let res := list_apply h' largs2 in
                  exact (h res) *) ]  
                  end
  | ConsQuantif ?largs' => 
      match type of h with
      | (forall x:?t, _) =>
          (* let y:= fresh x in *)
          (* intro y; *)
          refine (fun x: t => _);
          specialize (h x);
          refine_hd h largs' constr:(DCons _ x largs2)
      end
  | ConsEvar ?largs' => 
      match type of h with
      | (forall x:?t, _) =>
          (* morally this evar is of type t, don't know how to enforce this
             without having an ugly cast in goals *)
          let ev1 := open_constr:(_:t) in
          refine (let x:= ev1 in _);
          specialize (h x);
          subst x;
          refine_hd h largs' largs2
      end
  | ConsSubGoal ?largs' => match type of h with
                          | (forall x:?t, _) =>
                              let h' := fresh h in
                              (* create the user subgoal *)
                              assert(t) as h'
                              ;[ clear h
                               | exact (h h')
                                 (*let res := list_apply h' largs2 in
                                   exact (h res) *) ]   
                          end
  end.

(* Precondition: name is already fresh *)
Local Ltac espec_gen H l name :=
  (* let l := eval cbn [spec_interp] in (spec_interp args) in   *)
  (* let h := fresh name in *)
  (* morally this evar is of type Type, don't know how to enforce this
     without having an ugly cast in goals *)
  let ev1 := open_constr:(_) in
  assert ev1 as name
  ; [
      (refine_hd H l DNil)
    | ].
  
Local Ltac especialize_clear H args :=
  let temp := fresh H "temp" in
  espec_gen H args temp;
  [ | clear H;
      (* idtac "ICI: " temp; *)
      rename temp into H ].

Local Ltac especialize_autoname H args :=
  let name := fresh H "_inst" in
  espec_gen H args name.

Local Ltac especialize_clear_autoname H args :=
  let name := fresh H "_inst" in
  especialize_autoname H args name.

Notation "! X" := (ConsQuantif X) (at level 100) : specialize_scope.
Notation "? X" := (ConsEvar X) (at level 100) : specialize_scope.
Notation "# X" := (ConsSubGoal X) (at level 100) : specialize_scope.
Notation "§" := (SubGoalEnd) (at level 100) : specialize_scope.

Tactic Notation "especialize" constr(H) "at" constr(specarg) "as" ident(idH) :=
  espec_gen H specarg idH.
Tactic Notation "especialize"  constr(specarg) "as" constr(H) "at" ident(idH) :=
  espec_gen H specarg idH.

Tactic Notation "especialize" constr(H) "at" constr(specarg) :=
  especialize_clear H specarg.
