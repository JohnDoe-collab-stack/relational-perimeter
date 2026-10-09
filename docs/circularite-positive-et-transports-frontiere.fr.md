# Circularité positive et transports de frontière

Cette extension sépare les données positives de la circularité et l’obstruction au bouclage. Elle définit aussi des transports exacts de la frontière fermante équipée de sa jonction et de sa provenance. Les modules sont accessibles depuis `RelationalPerimeter.Constitution` ; `RelationalPerimeter.Constitution.PositivePresentation` s’importe seul, sans la couche historique obstruée.

## Données positives et obstruction

`PositiveCircularPresentation` reçoit les sortes explicites et implicites, la famille `Compatible`, les différences et leurs provenances, un nœud initial, une épine successive positive et la jonction fermante distinguée. `perimeterPositive` signifie que cette épine possède au moins une position non fermante. Cette interface reçoit la chaîne. La [formation positive du lot 2](formation-et-generation-positives.fr.md) construit désormais son déploiement depuis une histoire de pas admissibles ; elle reçoit toujours les primitives et une jonction distincte pour fermer la chaîne.

Les lectures des deux pôles sont ajoutées par `EndpointBoundary`. Ce type ne suppose pas leur séparation. `CircularClosureObstruction` est un enrichissement distinct : il reçoit un type de boucle, le passage d’une identification des pôles à une boucle, la contraction initiale produite par cette boucle et le rejet de la contraction. La séparation des pôles est démontrée depuis cet enrichissement.

Le modèle `Examples.positive` reçoit deux extensions : `identifiedBoundary` lit ses deux pôles dans `Unit`, tandis que `separatedBoundary` les lit dans `Bool` avec les valeurs `false` et `true`. La première possède des pôles identifiés et ne peut recevoir l’obstruction définie ici. La seconde reçoit une obstruction constructive. La chaîne positive et son témoin fermant restent littéralement les mêmes. Ce modèle établit que ces données positives n’imposent pas le rejet de toute identification. Il ne construit pas une histoire générée périodique : l’irréflexivité des curseurs du générateur historique reste une propriété distincte.

`CircularPresentation` étend désormais cette présentation positive avec ses champs historiques de pôles et d’obstruction. `endpointBoundary`, `closureObstruction` et `ofPositive` relient les deux interfaces. Les lois `positive_roundTrip`, `boundary_roundTrip`, `obstruction_roundTrip` et `historical_roundTrip` reconstruisent exactement les données, avec leurs témoins, sans changer l’épine ni la jonction. Les preuves du périmètre, du tournant et les consommateurs computationnels continuent d’utiliser cette interface historique.

## Frontière équipée

`ConstitutiveBoundary` retient une signature sélectionnée :

- les sortes explicite et implicite, la source fermante et la cible initiale ;
- la fibre de compatibilité de cette paire et sa jonction distinguée ;
- une différence et sa fibre de provenance, avec le témoin distingué de cette provenance.

`closingBoundary P` extrait ces données de la même présentation positive : la source est l’implicite terminal, la cible l’explicite initial, la jonction est `P.finalJunction`, la différence et la provenance viennent du nœud initial. Il ne génère aucune occurrence supplémentaire.

`BoundaryCarrierTransport` donne cinq transports exacts : sortes explicite, implicite et différence, puis les deux fibres sélectionnées. `BoundaryTransport` ajoute cinq lois : accord de la source, de la cible et de la différence, conservation de la jonction distinguée et conservation de la provenance distinguée. Les accords sont des champs distincts des deux lois de retour de chaque transport.

L’identité, l’inversion et la composition calculent ces accords. Les lois de composition, d’unité et d’inversion sont démontrées point par point sur les cinq porteurs. L’accord des applications inverses est dérivé de celui des applications directes. L’existence de tels transports est réflexive, symétrique et transitive, sans recours à une égalité globale de structures contenant des fonctions.

Le modèle `Examples.closingSwap` conserve les trois indices et possède des retours exacts sur toutes les fibres, mais échange les deux témoins `Bool` de compatibilité. Il ne peut donc être enrichi en `BoundaryTransport` avec ces mêmes applications. Les sondes de relecture établissent également l’indépendance de la loi de provenance : on peut conserver la jonction et échanger seulement les témoins de provenance.

## Rôle final et portée

`EquippedFinalRole B` stocke un témoin de la fibre fermante et sa loi d’accord avec la jonction distinguée. Sa source, sa cible et sa provenance sont lues depuis la frontière équipée qui l’indexe. Le rôle est habité et unique pour cette frontière ; un `BoundaryTransport` le transporte avec les accords de source, cible et provenance, et fournit les deux retours exacts.

Le rôle historique `FinalRequirement` reste disponible pour la classification des occurrences. Le nouveau rôle équipé expose une autre interface, consacrée à la conservation du témoin de frontière. Aucun de ces types n’est identifié à une occurrence engendrée. La possibilité de transporter leur porteur contractile vers `Unit` ne remplace pas les lois imposées aux morphismes de la frontière.

La portée des transports est **cette signature de frontière sélectionnée**. Ils ne conservent pas automatiquement toutes les fibres de `Compatible` ou `Provenance`, les fonctions de pôles sur toutes les différences, l’épine entière, l’ordre ou les histoires engendrées. La signature générale de quantité constitutive et la génération à plusieurs successeurs restent des portes de recherche distinctes.

Le [lot 3](transports-signature-et-formation.fr.md) fournit désormais une interface supplémentaire pour toutes les fibres, les épines et une formation reconstruite sur les mêmes états et pas. Ses accords de positions, d’ordre et de clôture sont prouvés séparément ; les pôles et l’obstruction restent à transporter.

La [frontière avant le choix de la jonction](frontiere-sans-jonction-choisie.fr.md) est désormais définie par `ClosingBoundaryShape`. Sa fibre fermante peut être vide ; `PointedClosingBoundary B` ajoute explicitement une jonction. Les retours exacts reconstruisent la frontière actuelle, et les modèles `Empty`, `Unit` et `Bool` distinguent existence, choix et unicité du rôle pour chaque choix. Les indices et la provenance initiale restent sélectionnés dans cette forme.

## Vérification

Les sources conservent la discipline constructive et un bloc terminal d’audit. Les modèles et les lois sont compilés avec le toolchain fixé par le dépôt. Une relecture IA indépendante a utilisé d’autres modèles de transport sur les cinq porteurs et deux échanges de témoins distincts ; son rapport est dans `research/agents/referee-positive-foundations/report.md`. La vérification humaine reste en attente ; les résultats sont classés T2 dans la carte Labyrinth.
