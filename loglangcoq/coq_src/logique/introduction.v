(** remove printing -> *)
(** remove printing forall *)
(** remove printing exists *)
(** remove printing ~ *)
(** remove printing => *)
(** remove printing \/ *)
(** remove printing /\ *)
(** printing -> $\longrightarrow$ #&#10230;# *)
(*moche printing => $\longrightarrow$ #&#10233;# *)
(** %\chapter{Introduction}%
    #<h1 class="libtitle">Introduction</h1># *)

(** * Objectif du document

Ce document sert de support aux cours NFP108 (partie logique) et
NFP120 (parties logique et sémantique des programmes) du CNAM.
L'objectif est double:

- faire une introduction à la logique, en particulier les notions
  de syntaxe, de sémantique et de système de déduction;
- mettre en évidence les liens entre la logique et l'étude des
  langages de programmation en abordant les mêmes notions de syntaxe,
  sémantique et système d'inférence pour ces langages. En effet un
  programme peut être vu comme une _formule_ avec une syntaxe et une
  sémantique particulières.


Le parti pris de ce document est de définir toutes les notions
logiques dans l'assistant de preuve
#<a href="http://coq.inria.fr">Coq</a>#%Coq\footnote{\url{http://coq.inria.fr/}}%.
Ces définitions sont donc écrites dans un langage formel dont vous
n'avez probablement pas l'habitude. Le but de cette introduction est
de fournir une bibliographie ainsi qu'un lexique permettant
d'appréhender ce langage formel. 

_IL NE S'AGIT PAS d'un cours d'utilisation de Coq (ce n'est
pas au programme), uniquement d'une aide à la lecture du document_.


* Que puis-je lire concernant ce cours?

Les supports de cours officiels sont sur le site du cours. Il s'agit
souvent simplement de la version PDF des fichiers Coq présentés en
cours. Le présent lexique est une aide à la lecture de ces fichiers.
Ci-dessous une liste de références couvrant le contenu du cours et
permettant d'approfondir les sujet abordés.

** Concernant la logique propositionnelle et la logique des prédicats

La logique des prédicats intègre en principe également les symboles de
fonctions, ce que nous ne faisons pas dans ce cours. Vous pouvez donc
ignorer cet aspect: les termes ne sont que des variables.

- #<a href="http://fr.wikipedia.org/wiki/Calcul_des_propositions">Wikipedia</a>#%\href{http://fr.wikipedia.org/wiki/Calcul_des_propositions}{\texttt{fr.wikipedia.org/wiki/Calcul\_des\_propositions}}% en
  particulier la section « Sémantique » (vous pouvez ignorer la partie
  « systèmes déductifs »).

- #<a href="http://fr.wikipedia.org/wiki/Calcul_des_prédicats">Wikipedia</a>#%\href{http://fr.wikipedia.org/wiki/Calcul_des_prédicats}{\texttt{fr.wikipedia.org/wiki/Calcul\_des\_prédicats}}%
   
- Sur la notion d'interprétation des formules:
  #<a href="http://fr.wikipedia.org/wiki/Théorie_des_modèles">Wikipedia</a>#%\href{http://fr.wikipedia.org/wiki/Théorie_des_modèles}{\texttt{fr.wikipedia.org/wiki/Théorie\_des\_modèles}}%


- Vous pouvez regarder également n'importe quel livre de
  logique, en général les premiers chapitre concerne la logique
  propositionnelle et les prédicats.

- R. Lassaigne et M. de Rougemont. « Logique et fondements de
     l'informatique ». Hermes, 1993.

- R. Cori et D. Lascar. « Logique mathématique: Calcul
  propositionnel, algèbres de Boole, calcul des prédicats ».
  Masson 1993.

- R. David, K. Nour et  C. Raffalli. « Introduction à la logique, 
  Théorie de la démonstration ».
  Dunod 2004.

- P. Lafourcade,  M. Lévy et S. Desvismes. « Logique et démonstration automatique,
  Informatique théorique - Introduction à la logique propositionnelle et 
  à la logique du premier ordre (Niveau A)  ».
  Ellipses 2012.

*)
(*
% \begin{frame}[containsverbatim]<presentation|handout>\frametitle{Bibliographie}
%   \label{bibliog}
%   \begin{itemize}
%   - \url{http://fr.wikipedia.org/wiki/Calcul_des_propositions} en
%     particulier la section « Sémantique » (vous pouvez ignorer la partie
%     « systèmes déductifs »).
%   - % Pour que l'url s'affichevc un accent correct:
%     \href{http://fr.wikipedia.org/wiki/Calcul_des_prédicats}
%       {\verb!http://fr.wikipedia.org/wiki/Calcul_des_prédicats!}
%     - Vous pouvez regarder également n'importe quel livre de
%       logique, en général les premiers chapitre concerne la logique
%       propositionnelle et les prédicats.
%     - Sur la notion d'interprétation des formules:
%       \href{http://fr.wikipedia.org/wiki/Théorie_des_modèles}%
%         {\verb!http://fr.wikipedia.org/wiki/Théorie_des_modèles!}
%       - R. Lassaigne et M. de Rougemont. \og Logique et fondements de
%         l'informatique\fg. Hermes, 1993.
%       - R. Cori et D. Lascar. \og Logique mathématique: Calcul
%         propositionnel, algèbres de Boole, calcul des prédicats\fg.
%         Masson, 1993. % url={http://books.google.fr/books?id=e9\_uAAAAMAAJ}
%       \end{itemize}
%     \end{frame}
*)
(** ** Concernant la méthode des tableaux

- #<a href="http://fr.wikipedia.org/wiki/Méthode_des_tableaux">Wikipedia</a>#%\href{http://fr.wikipedia.org/wiki/Méthode_des_tableaux}{\texttt{fr.wikipedia.org/wiki/Méthode\_des\_tableaux}}%
Sans regarder la section « metavariables et unification » qui est
hors-sujet pour nous.

** Concernant la sémantique des programmes

- Robert Harper.  Practical Foundations for Programming
  Languages. MIT Press.
- J. C. Mitchell.  Foundations for Programming Languages.
  MIT Press, 1996.
- B. C. Pierce.  Types and Programming Languages. MIT
  Press, 2002.
- B. C. Pierce et al, 
  #<a href="http://www.cis.upenn.edu/~bcpierce/sf/index.html">Software Foundations</a>#
 %Software Foundations: \href{www.cis.upenn.edu/~bcpierce/sf/index.html}{\texttt{www.cis.upenn.edu/\textasciitilde{}bcpierce/sf/index.html}}%.
  En Coq.


** Concernant la preuve de programme

- G. Winskel. « The Formal Semantics of Programming Languages:
  An Introduction ». MIT Press, 1993.
- Les documentations des outils de preuve de programmes: Frama-C,
  Spark/ADA, Microsoft Boogie, Java Extended Static Checking, etc.

* Qu'est-ce-que Coq?

#<a href="http://coq.inria.fr">Coq</a>#%Coq\footnote{\url{coq.inria.fr}}%
est un _assistant de preuve_. Autrement dit c'est un logiciel dans
lequel l'utilisateur peut écrire des définitions mathématiques
formelles, dans un style ressemblant à la programmation, et effectuer
des démonstrations sur ces définitions. Le cadre formel est
contraignant et la syntaxe rigide mais assurent que les démonstrations
sont correctes.

* Pourquoi utiliser Coq dans ce cours?

Parce-que l'expérience montre que les mathématiques formelles sont
plus compréhensibles (plus palpables), en particulier pour un public
d'informaticiens, quand elles sont présentées sous cette forme proche
de la programmation. Par ailleurs c'est un moyen pour l'enseignant de
s'assurer qu'il ne dit que des choses correctes d'un point de vue
logique...

Dans sa version précédente ce cours utilisait Prolog pour la même
raison. Nous avons décidé de passer à Coq pour deux raisons: d'une
part le langage Prolog est passé de mode (ce qui n'implique pas un
jugement de valeur de la part de l'auteur) et d'autre part parce-que
la sémantique de Prolog est difficile à appréhender et prend trop de
temps. NFP120 initialement était un cours d'un an et pas un semestre,
ce qui laissait du temps pour comprendre Prolog avant de s'en servir
pour définir et programmer les autres aspects du cours.

Dans ce cours il ne vous sera pas demandé de savoir utiliser Coq,
seulement de savoir lire les définitions contenues dans un fichier
Coq. Le but de ce lexique est de vous y aider.

*)