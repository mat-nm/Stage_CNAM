(** remove printing -> *)
(** remove printing forall *)
(** remove printing exists *)
(** remove printing ~ *)
(** remove printing => *)
(** printing -> $\longrightarrow$ #&#10230;# *)
From Stdlib Require Import FunInd.

(** %\chapter{Les tables de vérité des connecteurs}%
    #<h1 class="libtitle">Les tables de vérité des connecteurs</h1># *)

(** Les tables de vérité des opérateurs booléens sont des fonctions
    des booléens vers les booléens (le nombre d'arguments étant égal à
    l'arité du connecteur). Elle décrivent le résultat de
    l'application du connecteur sur des _booléens_. On généralisera le
    calcul d'un booléen à partir d'une _formule_ à l'aide de la notion
    d'interprétation. On présente une table de vérité en général par
    une grille énumérant toutes les valeurs possibles pour les
    arguments (une valuation des arguments par ligne) et pour chaque
    ligne la réponse du connecteur. *)

(** true et false sont des connecteurs à 0 arguments.
<<
      V
     ---
      V
>>
*)
Definition table_Vrai:bool := true.
(** <<
      F
     ---
      F
>>
*)
Definition table_Faux:bool := false.
(** La négation est un connecteur à 1 argument.
<<
      x  ¬(x)
     --------
      V   F
      F   V
>>
*)
Function table_Non(x:bool):bool :=
  match x with
    | true => false
    | false => true
  end.
(** Les autres connecteurs sont binaires. Ici le ou (noté ∨).
<<
      x  y  x∨y
     ----------
      V  V   V
      V  F   V
      F  V   V
      F  F   F
>>
*)
Function table_Ou(x y:bool):bool :=
  match x,y with
    | true,true => true
    | true,false => true
    | false,true => true
    | false,false => false
  end.
(** Et (noté ∧)
<<
      x  y  x∧y
     ----------
      V  V   V
      V  F   F
      F  V   F
      F  F   F
>>
*)
Function table_Et(x y:bool):bool :=
  match x,y with
    | true,true => true
    | true,false => false
    | false,true => false
    | false,false => false
  end.

(** La table de vérité de l'implication est parfois source d'erreur
    chez le débutant. Remarquez que lorsque [x] est faux, [x⇒y] est
    vraie indépendamment de [y].
<<
      x  y  x⇒y
     ----------
      V  V    V
      V  F    F
      F  V    V
      F  F    V
>>
*)
Function table_Implique(x y:bool):bool :=
  match x,y with
    | true,true => true
    | true,false => false
    | false,_ => true
  end.
