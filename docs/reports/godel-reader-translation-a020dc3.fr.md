# Revue de lecture et de traduction — obstruction gödelienne interne

Responsable : Codex (OpenAI), lecture autonome puis confrontation formelle.
Date : 16 octobre 2026.
Révision examinée : `a020dc3267c0670b1316b2b2f8d5b3259ab40d91`.

## Périmètre lu

La lecture a porté sur les deux passages canoniques français, sur les énoncés
et corps complets de `Diagonal.lean`, `PerimetralCorrespondence.lean` et de
l'instance HA, puis sur les trois fichiers de régression associés. Le rapport
indépendant Aristotle visant la même révision a été consulté seulement après
la reconstruction autonome du texte.

## Reconstruction autonome du texte

Le texte affirme, pour toute réalisation de l'interface générique annoncée,
qu'une exécution ordonnée produit une même phrase diagonale `G`, son point fixe,
un témoin de `Truth(G)` et une fonction `Proof(G) → Empty`. Cette production
certifiée constitue une présentation `P`, un tout réalisé et une continuation
stricte `H` avant toute hypothèse de fermeture.

L'hypothèse ultérieure d'admission de cette continuation dans le même régime
fournit un raffinement, son témoin positif et l'interprétation finale qui
réalise la tentative bilatérale. Chacune de ses totalisations fournit un noyau
de contraction. Pour les extrémités exactes `Truth(G)` et `Proof(G)`, le noyau
construit `Truth(G) → Proof(G)`. L'application à la vérité déjà produite, puis
à la non-prouvabilité certifiée du même `G`, donne `Empty` et seulement ensuite
`False`. Le rejet vise donc l'admission totalisante ; il ne nie ni la production,
ni le tout, ni la continuation.

## Confrontation aux preuves

Les types et les corps Lean confirment cette lecture, notamment les points qui
pourraient être perdus dans un résumé :

- les sorties positives sont des habitants de types dépendants, pas une
  conjonction propositionnelle ajoutée après coup ;
- aucune preuve de `False` n'est construite sans un terme d'admission ;
- les voies explicite et implicite passent toutes deux par la tentative,
  la totalisation, le noyau, `Truth(G) → Proof(G)`, puis `Empty` ;
- la phrase, la ressource et la provenance sont conservées, tandis que les
  histoires gödelienne et périmétrale ne sont pas déclarées littéralement
  identiques ;
- l'admission est consommée par le terme de preuve, même si l'effacement des
  preuves peut faire disparaître cette lecture du code compilé ;
- le tout et la continuation sont construits et co-retenus avant le rejet,
  sans être présentés comme les arguments logiques directs du dernier lemme ;
- HA ferme les contrats comme instance concrète et ne remplace jamais le cadre
  générique ;
- le texte ne revendique ni unicité architecturale, ni priorité historique,
  ni renforcement du théorème d'incomplétude classique.

Verdict de lecture : `REVIEWED`. Le texte français enregistré décrit fidèlement
la portée, les hypothèses, l'ordre constitutif et la conclusion des déclarations
citées. Aucune correction scientifique ou rédactionnelle n'est requise pour
cette revendication.

## Revue de traduction

Le registre ne lie cette revendication qu'à deux passages français :
`ENONCE_FORMEL_STABLE_GODEL.md` et
`docs/godel-false-temoin-interne.fr.md`. Il ne déclare aucun passage anglais
correspondant. La procédure scientifique précise qu'une synthèse uniquement
française ne requiert pas de traduction fictive.

Verdict de traduction : `NOT_APPLICABLE`. Aucune paire FR/EN n'existe dans le
périmètre enregistré ; il n'y a donc ni traduction à comparer ni divergence
linguistique à corriger.
