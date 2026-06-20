(** remove printing -> *)
(** remove printing forall *)
(** remove printing exists *)
(** remove printing ~ *)
(** remove printing => *)
(** remove printing \/ *)
(** remove printing /\ *)
(** printing -> $\longrightarrow$ #&#10230;# *)
(*moche printing => $\longrightarrow$ #&#10233;# *)
(* begin hide *)
Notation ℕ := nat.
(* end hide *)

(** * [forall], [exists], [/\], [\/], [->], etc

Dans ce cours on procédera de la manière suivante pour étudier les
différentes logiques au programme:

- premièrement définition syntaxique de la notion de formule sous
  la forme d'un type [formule] défini en Coq;
- définition de la notion de sémantique d'une formule;
- définitions et démonstrations des propriétés de la sémantique.

Il s'agit donc de définir mathématiquement la notion de formule. Pour
cela nous avons besoin du langage mathématique qui utilise lui aussi
sa propre notion de formule.

_Attention il y a donc deux types de formules_: d'une part les
formules Coq qui permettent de définir les propriétés dans le langage
formel de Coq, et d'autre part les éléments du type
[formule] que nous définissons dans le langage de Coq et
sur lequel nos définitions porterons. Dans la mesure du possible nous
essayons d'avoir deux jeux de connecteurs distincts.

Dans ce cours les symboles logiques en caractères ASCII seront
utilisés pour les formules Coq ([forall] pour la quantification
universelle, [~] la négation, [/\] pour la conjonction (et), [\/] pour
la disjonction (ou) etc) à l'exception de l'implication [->]. Nous
réserverons les notations symboliques non ASCII ([∀], [∃], [∧], [∨],
etc l'implication étant différenciée par la double flèche [⇒]) pour
les éléments du type [formule] (voir plus bas section Inductive, en
particulier le deuxième exemple).

Il est à noter que dans leur versions html, pdf ou texte les symboles
n'ont pas exactement le même aspect.
*)

(** * [Definition f:T := def.] *)

(**
Définit la constante [f], de type [T] dont la définition est [def]. Il
s'agit d'une syntaxe semblable à celle des langages de programmation.
Lorsque [f] est une fonction, les arguments de [f] sont mis en
paramètres de la manière suivante: [Definition f (p1:t1) ... (pn:t1) :
T := def.], où les [pi] sont les noms des paramètres et les [ti]
désignent leurs types.

Par exemple ci dessous la définition d'une fonction [table_Non] prend
un booléen en argument et retourne le booléen opposé. Notez au passage
la construction [match ... with ...] comparable dans une certaine
mesure à la commande [switch] de Java/C. *)

Definition table_Non(x:bool):bool :=
  match x with
    | true => false
    | false => true
  end.

(** Pour définir une fonction récursive, on utilisera la construction
[Fixpoint] (ou de manière équivalente [Function]). *)

(** * [Fixpoint f (x1:t1) ... (xn:tn) : T := def.] ou [Function f (x1:t1) ... (xn:tn) : T := def.] *)

(** Définition d'une fonction récursive. La syntaxe est comparable au
[Definition f (p1:t1) ... (pn:t1) : T := def.] ci-dessus, excepté que
[f] peut apparaître dnas sa propre définition (appel récursif).*)

(** * [Lemma X: Y.] ou [Theorem X:Y.] *)

(** Démarrage de la démonstration de la propriété [Y]. Le nom du
théorème (du lemme) une fois prouvé sera [X]. La preuve est ensuite
suivie d'un ensemble de \emph{tactiques} [Proof. ... End.] que vous
n'avez pas à comprendre (hors sujet pour NFP120, généralement masquées
dans les documents pdf et html). *)


(** * [Notation "xxx" := (yyy)] *)

(** Définit une notation [xxx] pour écrire [yyy] d'une
manière plus agréable. Ceci est très important, nous utiliserons dans
la mesure du possible les notations mathématiques usuelles pour la
logique et la sémantique. Souvent après la définition formelle d'une
notion nous lui adjoindrons une notation et nous utiliserons celle-ci
partout dans la suite. Voir par exemple plus bas dans la section «
Deuxième exemple ».


 *)

(** * Commandes usuelles *)

(** ** [Check x] ou [Print x.] *)

(** Demande au système le type ou la valeur de [x]. En général
la réponse obtenue est ajouté dans le document juste après la
commande. *)


(** ** [Module X.], [End X.], [Import X.] ou [Require X.] *)

(** Commandes de structuration des fichiers, vous pouvez les ignorer. *)

(** ** [Add Morphism ....] ou [Add Relation ...] *)

(** Commandes permettant de faciliter les preuves, vous pouvez les ignorer. *)

(** * [Inductive I : T := def]

Définit le type (l'ensemble) [I] par induction à l'aide des opérateurs
donnés dans [def]. Nous expliquons rapidement plus bas ce que signifie
une définition par induction. *)

(** ** Définition d'ensemble par induction *)

(** Il existe 3 méthodes canoniques pour définir un ensemble E, toutes
possibles dans coq:

- _Par extension_: On donne la liste exhaustive
  (_extensive_) des éléments. Par exemple: #E={0,1,2,3}#$E=\{0,1,2,3\}$.
- _Par intention_: On donne la propriété qui caractérise les éléments
  de l'ensemble. Par exemple: #E={ x | x ∈ ℕ ∧ x ≤ 3 }#$E=\{ x | x ∈
  ℕ ∧ x ≤ 3 \}$.
- _Par induction_: nous détaillons cette méthode ci-dessous.
  Dans ce cas on décrit l'ensemble des opérations permettant de
  _construire_ (d'énumérer, même indéfiniment) tous les éléments
  de l'ensemble. *)

(** ** Premier exemple: définition de ℕ par induction

Comment définir l'ensemble ℕ des nombres entiers naturels? Par
extension c'est impossible puisque l'ensemble est infini. Par
intention c'est possible si on a déjà défini un sur-ensemble (ℤ ou ℝ
par exemple) mais sinon c'est également impossible.

Intuitivement on écrirait ℕ=#{0,1,2,...}#$\{0,1,2,...\}$. Il ne
s'agit évidemment pas d'une définition correcte puisqu'elle n'exhibe
que trois entiers. Les points de suspension ne font pas partie du
langage mathématique formel.

On peut néanmoins définir ℕ de façon rigoureuse en suivant
cette intuition, en définissant non pas directement les éléments de
ℕ mais plutôt les _opérateurs_  permettant de
construire tous ses éléments.

On définit l'ensemble ℕ par induction de la façon suivante:

- l'élément 0 appartient à ℕ (0∈ℕ)
- Si n∈ℕ alors succ(n)∈ℕ
- ℕ est le plus petit ensemble clos par 0 et succ.

Autrement dit ℕ contient les éléments suivants:

 0, succ(0), succ(succ(0)), succ(succ(succ(0))), ...

Attention l'opérateur succ peut être vu soit comme une fonction
(telle que succ(n) retourne la valeur de n+1) soit comme un simple
constructeur c'est-à-dire que succ(n) est lui-même un élément de
l'ensemble défini et ne se calcule pas. Dans la syntaxe du logiciel
Coq on écrira: *)

Inductive nat : Type :=
     O  : nat
 | succ : nat -> nat.

(**
[Inductive nat:Type] signifie qu'on défini un nouvel
ensemble (un type) ℕ par induction. [O:nat]
signifie que [O] est un constructeur à zéro argument, et
[succ: nat -> nat]  signifie que [succ] est un
constructeur à un argument de type ℕ. *)

(** ** Deuxième exemple: les formules propositionnelles *)

(** De la même manière que ℕ peut être défini par induction,
l'ensemble des formules propositionnelles (sans variable), noté Fₚ
peut l'être aussi:

- ⊤∈Fₚ
- ⊥∈Fₚ
- si f∈Fₚ alors ¬ f∈Fₚ
- si f₁,f₂∈Fₚ alors f₁ ∨ f₂ ∈ Fₚ
- si f₁,f₂∈Fₚ alors f₁ ∧ f₂ ∈ Fₚ
- si f₁,f₂∈Fₚ alors f₁ ⇒ f₂ ∈ Fₚ
- Fₚ est le plus petit ensemble clos par les opérateurs ⊤,
  ⊥, ¬, ∨, ∧, ⇒.


Notez qu'on peut parler de _grammaire_ des formules, au sens où cette
définition inductive définit les règles de bonne formation des
formules. On voit donc souvent la définition ci-dessus exprimée de la
façon suivante (dite grammaire #<a href="http://fr.wikipedia.org/wiki/Forme_de_Backus-Naur">BNF</a>#%BNF\footnote{\url{http://fr.wikipedia.org/wiki/Forme_de_Backus-Naur}}%):


Fₚ ::= ⊤ | ⊥ | ¬ Fₚ | Fₚ ∨ Fₚ | Fₚ ∧ Fₚ | Fₚ ⇒ Fₚ


Dans la syntaxe Coq on définit Fₚ comme un type inductif [formule]
comme suit (voir également les fichiers Coq):*)

Inductive formule : Type :=
  | Vrai: formule
  | Faux: formule
  | Non: formule -> formule
  | Ou: formule -> formule -> formule
  | Et: formule -> formule -> formule
  | Implique: formule -> formule -> formule.

(** Des notations définies a posteriori permettent d'utiliser les
symboles usuels ([⊤] pour [Vrai], [⊥] pour [Faux], ¬[f] pour
[Non(f)], [f∨g] pour [Ou(f,g)] etc). *)
(* begin hide *)
Reserved Notation  "X ∨ Y" (at level 85,right associativity).
Reserved Notation "X ∧ Y" (at level 82,right associativity).
Reserved Notation "¬ X" (at level 80).
Reserved Notation "X ⇒ Y" (at level 86,right associativity).
(* end hide *)

Notation "⊤":= Vrai.
Notation "⊥":= Faux.
Notation "¬ X":= (Non X).
Notation "X ∨ Y":= (Ou X Y).
Notation "X ∧ Y":= (Et X Y).
Notation "X ⇒ Y":= (Implique X Y).

(** ** Troisième exemple: la propriété inductive "interprétation d'une formule"

En plus des ensembles, les définitions inductives permettent également
de définir des propriétés ou des relations. Par exemple nous donnons
ici la définition de la relation [I f b] qui est vrai lorsque le
booléen [b] est l'interprétation de la formule propositionnelle [f]
(Où [!], [&&] et [||] sont les opérateurs booléens usuels).

- [I ⊤ true]
- [I ⊥ false]
- Si [I f b] alors [I (¬ f) (!b)]
- Si [I f₁ b₁] et [I f₂ b₁] alors [I (f₁ ∨ f₂) (b1 || b2)]
- Si [I f₁ b₁] et [I f₂ b₂] alors [I (f₁ ∧ f₂) (f₁ && f₂)]
- Si [I f₁ b₁] et [I f₂ b₂] alors  [I (f₁ ⇒ f₂) (f₂ || ! f₁)]

En syntaxe Coq cela donne: *)
(* begin hide *)
From Stdlib Require Import Bool.
Notation "! x" := (negb x) (at level 40).
(* end hide *)

Inductive I: formule -> bool -> Prop :=
| I_Vrai: I ⊤ true
| I_Faux: I ⊥ false
| I_Non: forall f b₁ b, I f b₁ -> !b₁ = b -> I (¬f) b
| I_Ou: forall  f₁ f₂ b₁ b₂ b, I f₁ b₁ -> I f₂ b₂ -> b₁ || b₂ = b -> I (f₁ ∨ f₂) b
| I_Et: forall  f₁ f₂ b₁ b₂ b, I f₁ b₁ -> I f₂ b₂ -> b₁ && b₂ = b -> I (f₁ ∧ f₂) b
| I_Implique: forall f₁ f₂ b₁ b₂ b, I f₁ b₁ -> I f₂ b₂ -> (!b₁) || b₂ = b -> (I (f₁ ⇒ f₂) b).

(** Il y a un exemple (plus compliqué) de définition semblable dans le
développement Coq sur la logique des prédicats avec quantificateurs.
Il y a aussi un exemple similaire dans la partie sur la sémantique des
programmes.

Il faut lire une telle définition de la manière suivante: pour que la
propriété [I f b] soit vraie, il faut qu'il existe une
combinaison des opérateurs ayant comme conclusion [I f b].

Cette notion de combinaison d'opérateur (appelée également _arbre
  d'inférence_, _arbre de dérivation_, _arbre de preuve_
etc), fera l'objet de plusieurs séances de cours.
*)
