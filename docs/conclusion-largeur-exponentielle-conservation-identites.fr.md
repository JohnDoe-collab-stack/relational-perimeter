# Conclusion de la branche : largeur exponentielle et conservation séparée des identités

**Dans ce cadre, la constitution relationnelle des dépendances est primitive. Le calcul produit lui-même, pendant son exécution et à partir de ce qu’il a déjà produit, sa décomposition opérationnelle et détermine ainsi quelles alternatives doivent continuer à être traitées comme des obligations indépendantes.**

**Cette exécution ne produit pas d’explosion exponentielle de la largeur opérationnelle : bien que la lecture extensive du carrier des profils constitués ait une largeur 2ⁿ, le régime exécuté les regroupe en une seule obligation sans identifier les profils eux-mêmes.**

**Dans la classe binaire formalisée, une largeur opérationnelle exponentielle apparaît si et seulement si le régime impose de conserver séparément toute la multiplicité extensive, c’est-à-dire si son application `carry` est injective.**

**L’explosion exponentielle de la largeur opérationnelle est donc démontrée ici comme l’effet exact de cette exigence extensive de conservation indépendante, et non comme une conséquence nécessaire de la structure relationnelle du problème elle-même.**

## Résultat démontré

Pour toute `BinaryRelationalRoleExtensiveFamily`, tout problème de cette
famille et tout `ObligationRegime` sur le carrier source correspondant, Lean
démontre le véritable `iff` suivant :

```text
R.frontier.length = 2 ^ F.stageCount(p)
  ↔ Function.Injective R.carry
```

Autrement dit, dans la classe binaire formalisée :

> **La largeur de la frontière des obligations vaut exactement 2ⁿ si et
> seulement si le régime conserve injectivement chaque identité du carrier
> source comme obligation distincte.**

L'adressage séparé n'est pas une hypothèse supplémentaire. Il est construit à
partir de l'injectivité de `carry` et doit factoriser par les obligations du
régime :

```text
identité du carrier source
  ─carry→ obligation du régime
  ─address→ slot
```

La surjectivité de `carry` est un champ essentiel de `ObligationRegime`. Ni la
pleine largeur ni l'injectivité ne sont placées dans la définition du régime ;
les deux directions de l'équivalence sont démontrées.

Avant la spécialisation binaire, le théorème général est :

```text
longueur de la frontière des obligations
  = longueur de la frontière du carrier source
  ↔ Function.Injective R.carry
```

Le terme 2ⁿ provient du théorème séparé qui calcule la largeur de la
frontière source d'une histoire uniformément binaire.

## Conséquence mathématique

Le même carrier source admet deux régimes formellement construits.

Le régime identitaire conserve chaque profil source comme obligation
distincte :

```text
régime identitaire
  ⇒ Function.Injective carry
  ⇒ largeur des obligations = largeur source = 2ⁿ
```

Le régime exécuté est construit sur exactement le même carrier. Sa réduction
est lue dans une histoire dépendante construite étape par étape. La
décomposition de l’étape courante dépend uniquement de cette étape ; sa suite
commence dans l’état que celle-ci a produit. Pour chaque profil source,
`executedCausalNormalization` produit un profil d’occurrences cible et une
trace `ExecutedRoleProfileReduction` exactement indexée par cette source et
cette cible. Le cas transformé requiert l’action relationnelle effectivement
reconstruite, sa sortie exacte, la preuve séparée de préservation, la
non-identité de l’action sur la source exécutée et la distinction persistante
des occurrences ; le cas retenu requiert sa viabilité positive. Le profil
retenu est dérivé récursivement des licences exécutées.

`rawProducedTargetOccurrences` rassemble ensuite les cibles de tous les profils
sources sans perdre les traces qui les produisent. `producedTargetFrontier`
calcule leur image sans doublon. `computedTargetImageRegime` construit alors le
carrier d’obligations, sa frontière et son `carry` directement depuis cette
image : deux profils reçoivent la même obligation si et seulement si leurs
cibles produites sont égales. La convergence des traces démontre que cette
frontière contient exactement un élément :

```text
régime exécuté
  ⇒ largeur des obligations = 1
```

L’unicité de cette obligation n’est donc pas utilisée comme substitut à la
réduction. Les cibles et leurs traces sont construites avant le régime, dont le
carrier et le `carry` ne peuvent pas être fournis indépendamment.

Dans l'instance publique positive, deux profils sources sont construits comme
distincts tout en ayant la même obligation exécutée. Leur égalité d'obligation
n'établit aucune égalité dans le carrier source.

```text
distinction des identités du carrier source
  ≠ conservation comme obligations opérationnelles distinctes
```

La quantité exponentielle des profils sources ne suffit donc pas à imposer une
largeur opérationnelle exponentielle. Cette largeur apparaît exactement lorsque
le régime porte séparément toutes les identités sources.

Le régime exécuté ne compresse pas 2ⁿ obligations préexistantes. Avant son
introduction, il existe un carrier source de 2ⁿ profils distincts, dont
l’extensivité fournit la lecture quantitative ; leur statut d’obligations
opérationnelles n’est pas encore déterminé. La normalisation exécutée construit
ce statut pour chaque profil, la réalisation exacte en constitue l’image, puis
le régime en expose la frontière et la largeur. Le `iff` général s’applique
directement à ce régime sur ce même carrier ; aucun transport vers un autre
carrier n’intervient.

Le résultat central peut ainsi être formulé sans le réduire à un problème de
compression :

> **Dans la classe formalisée, l'explosion exponentielle de la largeur des
> obligations apparaît exactement lorsque le régime impose que toutes les
> identités structurelles soient conservées comme obligations distinctes et
> séparément adressables.**

## Stratification qui donne son sens au résultat

La constitution appartient exclusivement à la couche relationnelle. Des
relations primitives de source, de formation, de cible et de provenance,
accompagnées de leurs témoins, constituent les occurrences de rôle et leur
histoire dépendante.

```text
relations primitives + témoins
  → occurrences de rôle constituées
  → histoire relationnelle dépendante
  → profils complets d'occurrences
  → carrier source
```

Les profils sont des sélections dépendantes d'occurrences déjà constituées à
chaque rôle. Leur frontière complète et sans doublon est dérivée de l'histoire.

L'extensivité n'est pas une couche constitutive. Elle est seulement le readout
quantitatif de cette frontière déjà dérivée :

```text
carrier source
  → frontière complète des profils
  → readout extensif : longueur de la frontière
```

Depuis le même carrier source, un régime d'obligations peut être formé sans
dépendre du calcul de cette largeur. Sa propre largeur est un second readout.

```text
constitution relationnelle
  → carrier de profils
      ├→ readout extensif source
      └→ carry → régime d'obligations
                  → readout de la largeur des obligations
```

Le `iff` relie ces deux readouts ; il ne transforme pas le readout extensif en
principe de constitution.

Le nom Lean `RelationalRoleExtensiveFamily` doit être lu selon cette
stratification : `RelationalRole` qualifie la constitution de l'histoire et de
ses occurrences ; la largeur extensive est un readout dérivé. Ce nom ne
désigne pas une « extensivité relationnelle » qui constituerait ses propres
termes.

## Différence avec une lecture extensionnelle

Une lecture extensionnelle prend ses termes comme donnés et les rassemble dans
une collection. Elle ne contient pas leur constitution. Le cadre relationnel
expose en amont les relations et les témoins qui constituent les occurrences,
puis maintient la distinction entre le carrier ainsi obtenu, sa lecture
quantitative et son portage opérationnel.

La différence ne s'énonce donc pas comme une opposition entre une
« extensivité classique » et une « extensivité relationnelle ». Elle réside
dans l'accès formel à une couche constitutive que la lecture extensionnelle ne
contient pas, puis dans la séparation entre identité structurelle et statut
d'obligation opérationnelle.

## Portée exacte

Le théorème porte sur l'égalité de deux largeurs finies et sur la conservation
injective des identités de profil par un régime surjectif d'obligations. Dans
la sous-classe binaire, la largeur source vaut exactement 2ⁿ. Dans la classe à
arités variables, elle vaut le produit des arités locales réalisées.

Il ne s'agit pas d'une borne universelle de temps ou de mémoire, ni d'une
formalisation de tout arbre adaptatif possible. Il s'agit d'une
caractérisation exacte du moment où la largeur de la frontière des obligations
reprend intégralement la quantité lue sur le carrier source.
