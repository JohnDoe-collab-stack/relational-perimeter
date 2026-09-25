# Décomposition opérationnelle endogène

## Résultat

La construction exhibe une recherche dont la **décomposition opérationnelle
est un produit du calcul, et non une donnée de sa structure de branchement**.

L’ouverture produit une multiplicité structurelle. Ce qui détermine si cette
multiplicité doit être portée comme plusieurs obligations indépendantes est une
transformation qui :

1. n’existe pas comme donnée avant que l’exécution ne la reconstruise ;
2. est trouvée par un travail effectivement exécuté, qui échoue sur la plupart
   des relations candidates ;
3. agit sur des continuations arbitraires, avant que l’on sache quelle
   alternative est acceptée ;
4. possède une preuve de préservation distincte, qui autorise l’abandon d’une
   alternative pour le critère considéré, sans identifier les alternatives et
   sans prouver l’impossibilité de celle qui est abandonnée.

Le résultat de la transformation fournit ensuite l’état retenu, la graine,
l’histoire des décisions et la provenance utilisés par l’étape suivante. La
reconstruction suivante a donc lieu sous des conditions produites par la
précédente.

En bref, **la multiplicité structurelle et l’indépendance opérationnelle sont
séparées, et cette séparation est décidée pendant le calcul, par le calcul, à
partir de matériaux produits par le calcul**.

![Architecture exécutée de la décomposition opérationnelle endogène](figures/endogenous-operational-decomposition.svg)

## Chaîne exécutée

Pour chaque entrée, une récursion faisant autorité construit la chaîne suivante :

```text
état constitué
  → racine opérationnelle engendrée
  → extraction endogène des candidats
  → filtrage par la provenance produite
  → ouverture structurelle en deux enfants distincts
  → recherche exécutée d’une relation entre eux
  → compilation et validation du transport découvert
  → application à une continuation arbitraire
  → preuve séparée de préservation de l’acceptation et de la viabilité
  → cible retenue et détermination booléenne exécutée
  → transmission de la graine, de l’histoire des décisions et de la provenance
  → racine, domaine de candidats et recherche de relation suivants
```

Le calcul public est
`ConstitutiveSearch.EndogenousDecomposition.executeConstitutiveResolution`.
Son résultat est projeté depuis `executeConstitutiveExecutionHistory` ; aucune
seconde exécution ne fournit parallèlement l’histoire publique, l’état terminal,
la décision ou la comptabilité.

La frontière d’entrée suit la même discipline causale. Le premier état transmis
est construit depuis le point terminal enregistré par l’initialisation mesurée
effectivement exécutée. Sa génération est ensuite prouvée égale à la génération
canonique ; aucune source reconstruite indépendamment ne remplace celle qui a
été produite.

## Ce que les types séparent

Les types maintiennent visibles les distinctions suivantes :

- la génération de deux alternatives n’est pas leur indépendance
  opérationnelle ;
- une application totale sur les continuations n’est pas son théorème de
  préservation de l’acceptation ;
- la préservation relative à un critère n’est pas l’égalité des alternatives ;
- l’absorption d’une obligation n’est pas une preuve que l’alternative absorbée
  est impossible ;
- l’égalité d’une lecture n’est pas l’égalité de la recherche constituée ;
- la formation causale d’une graine est distinguée de la variation de sa
  valeur ;
- un transport exact réversible n’est pas le transport dirigé utilisé pour
  l’absorption.

Cette dernière distinction raccorde directement la computation aux quatre
modules fondamentaux. `ExactTypeTransport` enregistre un transport réversible
entre carriers. `AcceptingContinuationTransport`, au contraire, contient une
application dirigée et une loi de préservation séparée. Le résultat
computationnel dépend de ce second transport sans le renforcer silencieusement
en équivalence.

## Stabilité opérationnelle endogène et branchement exponentiel

Le cadre constitue d’abord les objets structurés sur lesquels la computation
agit. La computation constitue ensuite leur statut opérationnel en déterminant
si des alternatives structurellement distinctes doivent être portées comme des
obligations indépendantes.

Cet énoncé est désormais explicite dans les types. Chaque
`ThreadedConstitutiveRoleStage` porte trois frontières typées issues de la même
découverte exécutée :

```text
source singleton [parent]
  ↔ ouverture binaire [left, right]
  ↔ singleton retenu [right]
```

La première équivalence est l’ouverture structurelle exacte. La seconde est
l’absorption préservant l’acceptation, fournie par la relation reconstruite à
ce stade. Elle ne prouve ni l’égalité des deux enfants ni l’impossibilité de
l’enfant absorbé. La queue dépendante part de la condition produite par le
singleton retenu ; sa largeur initiale est donc définitionnellement la largeur
retenue du stade précédent.

`OperationalStabilityCertificate` est calculé depuis la même
`ThreadedConstitutiveRoleHistory` qui indexe l’exécution causale faisant
autorité. Pour une exécution de `n` stades, il établit :

```text
trace des largeurs = [1, 2, 1, 2, ..., 1]
longueur de la trace = 2 * n + 1
toute largeur enregistrée vaut 1 ou 2
toute largeur enregistrée est inférieure ou égale à 2
```

La stabilité sous les transformations reconstruites empêche ainsi que la
répétition de l’ouverture binaire structurelle s’accumule en largeur
opérationnelle exponentielle dans la famille construite. Cet énoncé porte sur
le nombre d’obligations qui doivent demeurer simultanément indépendantes. Il se
distingue du travail total : la recherche de relation, les candidats en échec,
la compilation, la validation, l’exécution, la transmission et la lecture
restent mesurés séparément.

La construction situe également la frontière exacte d’une description par
l’état seul. L’état produit par l’exécution et une constitution bloquée construite
contrefactuellement depuis la même origine exécutée ont la même projection
autorisée : affectation, génération et graine. La constitution retenue construit
positivement un témoin complet de stabilisation en un stade et porte le profil
`some [1, 2, 1]` ; la constitution
bloquée n’admet aucun tel témoin et porte le profil `none`. Ni l’habitabilité du
témoin ni le profil ne se factorisent donc par cette projection, et aucune vue
calculée uniquement depuis elle ne permet de les retrouver.

Le rapport aux analyses classiques de stabilité est ainsi délimité avec
précision. Une telle analyse peut étudier une dynamique après fixation de ses
variables d’état et de sa loi d’évolution. Le résultat formel porte ici sur une
question constitutive antérieure : le statut d’alternatives structurellement
distinctes comme obligations opérationnelles indépendantes est lui-même
reconstruit pendant l’exécution. Une description d’état enrichie pourrait bien
sûr porter cette évidence constitutive ; le théorème établit exactement que la
projection spécifiée, et toute vue se factorisant par elle, ne la porte pas.

## Évidence exposée par le dépôt

Le module public de formulation est
[`EndogenousOperationalDecomposition.lean`](../RelationalPerimeter/Computation/EndogenousOperationalDecomposition.lean).
Il expose des déclarations sans axiome pour :

- la distinction structurelle des alternatives ouvertes ;
- la transformation totale de continuations arbitraires ;
- la preuve séparée de préservation de l’acceptation ;
- le transport de la viabilité et la préservation exacte de la viabilité de la
  frontière ;
- le profil exact `1 → 2 → 1` à chaque stade exécuté, la trace alternée de
  longueur `2n + 1` et sa borne uniforme par `2` sur l’histoire faisant
  autorité ;
- le raccord définitionnel entre le singleton retenu et la condition dépendante
  suivante ;
- l’indépendance du pas complet à l’égard d’une preuve d’acceptation ;
- l’absence de toute étape construite et de toute histoire descendante faisant
  autorité de longueur positive après l’échec de la découverte ;
- l’échec de chaque relation candidate leurre engendrée et le nombre exact de
  tentatives précédant la réussite de la découverte ;
- la loi exacte des tentatives filtrées par la provenance et la croissance
  stricte du compteur total de recherche de relation émis par la récursion
  faisant autorité, en plus de la croissance de la recherche locale de
  référence ;
- la construction du premier état transmis depuis le point terminal de
  l’initialisation mesurée ;
- la formation, au niveau des constructeurs, de la graine et du faisceau
  d’extraction suivants à partir de l’état exécuté, distincte des preuves
  ultérieures de leur égalité canonique ;
- la consommation de la graine et de la provenance produites par la découverte
  suivante ;
- des lectures projetées égales dont les traces candidates constituées
  diffèrent ;
- des comparaisons contrefactuelles construites depuis une même origine
  exécutée : la comparaison de l’état retenu avec l’état à histoire effacée
  sépare les traces candidates constituées, tandis que la comparaison avec
  l’état bloqué sépare les histoires décisionnelles et les résultats de la
  découverte malgré l’accord de toute donnée projetable autorisée ; les
  comparateurs effacé et bloqué ne sont pas eux-mêmes émis par la récursion
  faisant autorité ;
- la non-factorisation du résultat suivant par la projection autorisée sur la
  paire séparatrice : la projection lit l’affectation, la génération et la
  graine de recherche, dont les valeurs sont délibérément égales pour les deux
  comparateurs, tandis qu’un élément canonique de référence du même domaine
  prouve que la projection elle-même est non constante ;
- la construction positive d’un témoin complet de stabilisation pour la
  constitution retenue, l’impossibilité d’un tel témoin pour la constitution
  bloquée, leurs profils exacts `some [1, 2, 1]` et `none`, ainsi que la
  non-factorisation de l’habitabilité du témoin et du profil par la projection
  autorisée ou par toute vue de celle-ci ;
- une comptabilité mesurée canonique, à propriétaire unique, et les bornes
  polynomiales portant sur le travail explicitement instrumenté de la famille
  construite.

L’implémentation complète demeure sous
`RelationalPerimeter/Computation/ConstitutiveSearch/`. Le module de formulation
est un point d’entrée vers cette implémentation, non son remplacement. Deux
suites de régression protègent les énoncés de production correspondant aux
quinze contre-épreuves adversariales énumérées indépendamment, ainsi que la
surface plus large de l’exécution et de sa comptabilité ; elles ne revendiquent
pas une identité textuelle avec des fichiers historiques d’audit qui ne sont
distribués dans aucun des deux dépôts.

## Portée exacte

Le résultat est constructif, exécutable, uniformément indexé par la profondeur
et sans axiome. Il est instancié sur une famille SAT explicite engendrée, fondée
sur une symétrie par inversion de polarité. La découverte accomplit un travail
décidable réel, rejette des candidats leurres, et le compteur de tentatives émis
par la récursion faisant autorité, filtrée par la provenance, obéit à une loi
générale exacte et croît strictement avec les entrées successives. L’échec de la
découverte ne produit ni étape ni histoire descendante faisant autorité de
longueur positive.

La recherche suivante dépend du résultat précédent en deux sens différents :

- matériellement, la comparaison contrefactuelle de l’état produit avec des
  états effacé et bloqué construits depuis la même origine exécutée montre
  que l’histoire des décisions et la provenance peuvent changer le domaine de
  candidats et le résultat de la découverte suivante ; les états comparateurs
  sont des constructions d’analyse, non des états supplémentaires émis par la
  récursion faisant autorité ;
- causalement, la racine suivante est formée depuis une graine lue sur l’état
  produit, tandis que l’invariant de cet état établit aussi sa valeur canonique
  exacte.

Le dépôt n’établit ni `P = NP`, ni `P ≠ NP`, ni un solveur polynomial pour des
instances SAT arbitraires, ni un théorème portant sur tout espace de recherche.
Ses bornes polynomiales concernent des compteurs explicitement produits et le
paramètre unaire de la famille construite. Ces limites ne réduisent pas le
phénomène exhibé ; elles délimitent exactement le lieu où il est démontré.
