(* On met ici toutes les vérification de présence d'axiome. On les a
   sortis des fichiers car "coqc -vos" échoue sur ce genre de
   commande. Si on veut faire la même chose poure semantique.v & co il
   faudra utiliser una utre fichier car les il y a des
   incompatibilités de notation entre la logique et la sémantique (à
   changer). *)
Require deduction_naturelle.
Print Assumptions deduction_naturelle.completness.

Require Import logique_predicats_avec_quantificateurs.
Print Assumptions tableau_forall.
Print Assumptions tableau_exist.
Print Assumptions interp_def_tot.
