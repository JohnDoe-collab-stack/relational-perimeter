# Formation et génération positives

Le lot 2 construit des histoires finies de pas admissibles, leur déploiement positif et leur clôture explicite. Le [plan de poursuite](plan-suite-fondations-positives.fr.md) situe ce résultat après la frontière sans jonction choisie et avant les transports de familles relationnelles complètes.

Les sources sont [PositiveGeneration.lean](../RelationalPerimeter/Constitution/PositiveGeneration.lean), [le pont historique](../RelationalPerimeter/Constitution/PositiveGenerationBridge.lean) et [les modèles séparateurs](../RelationalPerimeter/Constitution/PositiveGenerationExamples.lean).

## Ce que reçoit la formation

`PositiveFormation` reçoit les cinq sortes et familles primitives, un type `State`, une lecture `node : State → LocalNode`, une famille de pas `Step source target` et la lecture de leur compatibilité entre les nœuds correspondants.

Cette interface fournit une notion de pas admissible. Elle ne suppose ni un pas depuis chaque état, ni un successeur unique, ni une clôture. Les nœuds reçus sont déjà équipés de leurs compatibilités internes et de leurs provenances. L’interface n’engendre pas ces primitives et n’impose pas une loi générale de conservation de provenance entre deux pas ; une telle loi est une donnée supplémentaire de la formation qui l’exige.

`PositiveFormation.link step` regroupe les deux nœuds et le témoin `compatibility step`. Les données supplémentaires éventuelles de `Step` restent stockées dans l’histoire.

## Construire une histoire et son déploiement

`PositiveHistory F source target` est une histoire finie composable :

- `nil` reste sur un même état sans pas ;
- `cons step tail` ajoute un pas dont la cible est la source de la suite.

Le raccord des états est porté par les indices. L’histoire reçoit des pas concrets dans `Type` ; elle ne les extrait pas depuis une existence propositionnelle.

`deploy` construit `PerimeterSpine` par récursion : `nil` devient une frontière, chaque `cons` ajoute une avancée avec le témoin lu depuis son pas. `deploy_start` et `deploy_final` établissent les accords exacts avec les nœuds lus depuis les états de départ et de terme.

`append` compose deux histoires dont les états se raccordent. Les deux unités et l’associativité sont prouvées. Du côté de l’épine, `PerimeterSpine.append` reçoit une suite indexée par le nœud terminal réel ; `appendAlong` transporte une suite depuis un nœud égal à ce terme.

La loi de composition est donc explicite :

```text
deploy (append first second)
  = appendAlong (deploy first) (deploy_final first) (deploy second)
```

La réindexation du suffixe fait partie de cet énoncé. Une simple ressemblance des nœuds ne remplace pas le raccord exact.

## Positions et témoins de chaque pas

`PositiveHistory.Occurrence history` distingue les positions des pas dans une histoire donnée : `here` désigne le premier pas ; `later` place une occurrence dans la suite. L’histoire vide n’en possède aucune.

`toPosition` et `fromPosition` relient ces occurrences aux `NonClosingPosition` du déploiement. `positionTransport` fournit les deux applications et leurs deux retours exacts. Une histoire contenant un pas possède `here`, dont l’image donne une position non fermante.

`linkAt` lit les nœuds et le témoin de compatibilité du pas situé à une occurrence. `deploy_link_exact` démontre que sa lecture depuis l’épine déployée conserve exactement le paquet `SuccessiveLink` : nœud source, nœud cible et témoin de compatibilité choisi. Les différences et provenances internes sont conservées dans ces nœuds.

La portée de cette fidélité est précise. Deux pas différents peuvent avoir la même lecture de compatibilité et les mêmes nœuds. Le déploiement ne fournit pas un inverse de toutes les données de `Step`, et l’équivalence des positions n’est pas une équivalence entre toutes les histoires et toutes les épines. Le nouveau type d’occurrence désigne une position de cette histoire positive ; il n’est pas identifié automatiquement aux occurrences du générateur historique strict.

## Clôture après le déploiement

`history.boundaryShape` lit la source implicite terminale, la cible explicite initiale, la différence et la provenance initiales. Il ne reçoit aucune jonction. `boundary_source_exact` raccorde sa source au nœud de l’état terminal.

`toCircular` reçoit ensuite deux données : une occurrence attestant la positivité et un témoin concret dans `ClosingWitness history.boundaryShape`. Il construit `PositiveCircularPresentation`. Les accords `toCircular_initial`, `toCircular_deployment`, `toCircular_junction` et `toCircular_boundary` conservent respectivement le nœud initial, l’épine construite, la jonction choisie et la frontière du lot 1.

Un pas ne prouve pas l’existence de cette jonction. L’histoire vide est distinguée même si son nœud possède une compatibilité interne. Positivité et clôture sont deux obligations séparées.

`PositiveGenerationBridge.lean` ajoute les lectures de pôles et l’obstruction par `toHistorical`. Les trois couches reçues et le déploiement ont leurs accords exacts. Ce pont importe les machines historiques ; le module de formation et de déploiement ne les importe pas et ne consomme aucun rejet de contraction.

## Continuation choisie

`ChosenPositiveContinuation F` fournit un successeur et un pas depuis chaque état. C’est une interface supplémentaire, qui peut ne pas exister pour une formation donnée.

`walk source count` construit une histoire de longueur d’itération choisie, avec son état terminal. `walk_successor_positive` fournit une occurrence lorsque le nombre de pas demandé est un successeur. Ce compteur pilote cette construction ; il n’est pas une nouvelle définition de la quantité structurelle du périmètre.

## Modèles séparateurs

| Modèle | Données et résultat |
|---|---|
| Dirigé | Un pas de `false` à `true` se déploie positivement, mais la fibre fermante de `true` vers `false` est `Empty`. Aucun pointage ne peut fermer cette chaîne. Aucun pas ne part de `true`, donc une continuation choisie globale est impossible. |
| Fermé | Une histoire sur `Unit` lit un témoin de pas `true` et reçoit séparément une jonction `false`. Elle produit une présentation positive puis une présentation historique avec lectures de pôles et obstruction conservées. |
| Deux successeurs | Depuis le même état `false`, deux histoires admissibles aboutissent à des nœuds distincts. Deux continuations choisies donnent des successeurs différents. |
| Nœud répété | Deux pas lisent le même nœud brut, mais leurs occurrences et positions déployées sont distinctes. Leurs témoins de pas `true` et `false` restent distingués. |

Ces modèles séparent génération, clôture et détermination du successeur. Le dernier est une histoire finie dans la nouvelle interface ; il ne démontre pas une périodicité du générateur historique libre à curseurs stricts.

## Vérification et travaux suivants

Les 79 déclarations des trois modules ont leurs audits terminaux. Le build complet réussit avec 109 tâches et le contrôle global du dépôt vérifie 112 fichiers Lean. La [revue indépendante](../research/agents/referee-positive-generation/report.md) accepte le lot dans sa portée et a compilé 38 déclarations de sonde sans axiomes. Les journaux de cette itération sont dans `labyrinth/evidence/generation-*.log`. Les résultats restent T2, avec vérification humaine en attente.

Les [transports du lot 3](transports-signature-et-formation.fr.md) et la [classification relative des rôles du lot 4](classification-roles-equipes.fr.md) sont réalisés. Le tournant couplé à une génération à plusieurs successeurs, la rigidité et une propriété universelle des histoires restent des questions distinctes. La génération est constructive relativement à `PositiveFormation`, et reçoit toujours ses primitives et ses pas admissibles.
