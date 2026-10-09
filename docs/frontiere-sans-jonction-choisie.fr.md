# Frontière avant le choix de la jonction

Le lot 1 du [plan de poursuite](plan-suite-fondations-positives.fr.md) distingue la forme d’une frontière, l’existence d’un témoin fermant, son choix et l’unicité du rôle associé à ce choix. Les constructions sont dans [ClosingBoundary.lean](../RelationalPerimeter/Constitution/ClosingBoundary.lean), les modèles dans [ClosingBoundaryExamples.lean](../RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean). Les deux modules sont exportés par `RelationalPerimeter.Constitution` et la racine publique.

## La forme et sa fibre fermante

`ClosingBoundaryShape` reçoit les sortes explicite et implicite, `Compatible`, la source et la cible, les différences et leurs provenances, ainsi que la différence initiale et sa provenance choisie. Elle ne reçoit pas de jonction fermante.

Le terme « sans jonction choisie » porte uniquement sur ce témoin : les indices et la provenance initiale sont encore sélectionnés. La forme n’est pas une signature entièrement dépourvue de données distinguées.

`ClosingWitness B` est la fibre `B.Compatible B.source B.target`. Elle peut être vide, posséder un seul témoin ou en posséder plusieurs. `PointedClosingBoundary B` stocke une jonction dans cette fibre ; son index fixe les autres données.

Le constructeur `B.point junction` reçoit un témoin concret dans `Type`. `B.pointingTransport` donne un `ExactTypeTransport` entre les témoins de clôture et les enrichissements pointés, avec deux lois de retour. Cette équivalence conserve le témoin choisi.

## Existence et données constructives

`nonempty_pointed_iff` établit :

```text
Nonempty (PointedClosingBoundary B) ↔ Nonempty (ClosingWitness B)
```

L’énoncé et ses deux implications restent dans `Prop`. Il ne fournit pas une fonction qui extrait une jonction dans `Type` depuis la seule preuve `Nonempty`. Pour construire un enrichissement utilisable comme donnée, le constructeur reçoit explicitement le témoin.

`noPointingOfEmpty` montre qu’une fibre sans témoin interdit tout enrichissement pointé. `nonempty_finalRole_iff` relie également l’existence d’un choix accompagné d’un rôle à l’habitation de la fibre. `noFinalRoleOfEmpty` interdit ce couple si la fibre est vide.

## Raccord exact à la frontière actuelle

`ConstitutiveBoundary.toClosingBoundaryShape` oublie seulement la jonction ; `toPointedClosingBoundary` la conserve dans l’enrichissement indexé. Dans l’autre sens, `PointedClosingBoundary.toConstitutiveBoundary` réassemble tous les champs.

Trois retours sont démontrés :

- `shape_roundTrip` retrouve la forme depuis un enrichissement reconstruit ;
- `pointing_roundTrip` retrouve l’enrichissement et sa jonction ;
- `boundary_roundTrip` reconstruit exactement la `ConstitutiveBoundary` actuelle.

La frontière actuelle conserve ainsi sa signature et ses consommateurs. `shape_fibre_nonempty` précise une limite de l’oubli : la forme issue d’une frontière déjà équipée possède forcément un témoin. Les formes à fibre vide doivent être construites avant cet enrichissement ; elles ne proviennent pas de l’oubli d’une jonction existante.

## Unicité relative au choix

Pour un enrichissement `pointed`, `pointed.FinalRole` est le rôle équipé de la frontière reconstruite. `finalRole` en fournit un habitant ; `finalRole_unique` établit l’égalité de deux rôles sur le même choix. `finalRole_junction` lit leur accord avec la jonction de cet enrichissement.

La quantification « sur le même choix » est essentielle. L’unicité de chaque rôle ne force ni l’unicité des témoins de clôture, ni celle des enrichissements d’une même forme. Elle ne donne pas non plus une classification complète des rôles circulaires ou une rigidité générale des réalisations.

## Trois modèles

| Modèle | Fibre fermante | Résultat |
|---|---|---|
| `emptyShape` | `Empty` | Aucune jonction, aucun enrichissement pointé, aucun choix accompagné d’un rôle |
| `unitShape` | `Unit` | Jonction disponible et unique ; rôle associé unique |
| `boolShape` | `Bool` | Deux choix distincts sur la même forme ; chacun possède un rôle unique |

Le modèle vide est construit directement avec des indices et une provenance initiale disponibles. `empty_not_from_constitutive` démontre qu’il ne peut être l’oubli d’une frontière actuelle déjà équipée.

Dans le modèle `Bool`, `falsePointing` et `truePointing` ont la même forme et des jonctions différentes. Les rôles canoniques correspondants lisent des témoins différents. `bool_pointing_fibre_not_unique` et `bool_closing_fibre_not_unique` réfutent explicitement le passage de l’unicité du rôle pour chaque choix à l’unicité globale du choix.

## Portée et validation

Les 43 déclarations nouvelles sont constructives et disposent de leurs audits terminaux. Les modèles et l’import public sont compilés ; le build global réussit avec 106 tâches et le script du dépôt contrôle 109 fichiers Lean. Les journaux de cette itération sont dans `labyrinth/evidence/closing-*.log`. La [relecture indépendante](../research/agents/referee-closing-boundary/report.md) accepte le lot dans cette portée ; ses propres sondes comportent 20 déclarations auditées sans axiomes.

Le résultat concerne la frontière de clôture et son enrichissement par un témoin. Il ne construit pas encore les pas de génération positive, le transport de toutes les fibres relationnelles, ni la grammaire complète des rôles. Ces constructions restent les lots suivants du plan. Les résultats formels restent T2 avec une vérification humaine en attente.
