# Classification relative des rôles équipés

Le lot 4 définit une grammaire de rôles pour une même présentation circulaire positive : une branche intérieure lisant un lien à une position, et une branche finale lisant la frontière équipée. Leur classification a deux retours exacts et commute avec les transports du lot 3. Le [plan de poursuite](plan-suite-fondations-positives.fr.md) recense les constructions et les questions restantes.

## Rôles intérieurs et données lues

[CircularRoles.lean](../RelationalPerimeter/Constitution/CircularRoles.lean) définit `EquippedInteriorRole P` avec une position non fermante, un paquet `SuccessiveLink` et l’égalité de ce paquet à celui lu sur l’épine de `P` à cette position.

Le paquet contient les nœuds source et cible entiers ainsi que leur témoin de compatibilité. Chaque nœud contient aussi sa différence, sa provenance et sa compatibilité interne. L’accord porte donc sur ces données concrètes, pas seulement sur l’habitation d’une fibre.

`canonical` construit le rôle à une position. `ext` prouve qu’une même position détermine le même rôle équipé dans cette présentation. `positionTransport` fournit deux applications avec deux retours exacts entre positions et rôles intérieurs. Pour une présentation construite depuis une histoire positive, `occurrenceTransport` raccorde également les occurrences aux rôles ; `occurrence_link_readout` retrouve le paquet lu dans l’histoire.

Deux positions différentes peuvent lire le même paquet de nœuds et de compatibilité sans être le même rôle. Les modèles transportés vérifient cette distinction.

## Branche finale et classification

`CircularRole P` a deux constructeurs :

- `interior`, recevant un `EquippedInteriorRole P` ;
- `final`, recevant un `EquippedFinalRole (closingBoundary P)`.

Le rôle final reste celui du socle : son témoin est exactement la jonction choisie, tandis que source, cible, différence et provenance sont lus dans la frontière qui l’indexe. Son unicité est relative à ce choix.

`classify` lit une position intérieure ou le marqueur final `Unit`. `assemble` reconstruit le rôle équipé correspondant à partir de la **même présentation**, qui fournit ses témoins. Les deux retours sont prouvés ; `classificationTransport` donne :

```text
CircularRole P ↔ NonClosingPosition P.perimeter ⊕ Unit
```

`exhaustive` couvre les rôles de cette grammaire par un rôle intérieur canonique ou le rôle final canonique. `branches_distinct` sépare les constructeurs. Cette exhaustivité est relative au type déclaré ; elle ne classe pas tous les rôles que l’on pourrait définir dans une extension.

`generatedPosition` lit `some position` sur la branche intérieure et `none` sur la branche finale. La jonction ne crée donc pas une position ni une occurrence engendrée supplémentaire dans cette classification. Cela n’interdit pas qu’une autre histoire prolonge le périmètre avec ses propres occurrences.

## Raccord historique et réalisation

[HistoricalRoleBridge.lean](../RelationalPerimeter/Constitution/HistoricalRoleBridge.lean) relie exactement `FinalRequirement P` au rôle final équipé de la présentation positive parente du même `P`. Le marqueur historique ne porte pas seul une jonction : la présentation fixée fournit le choix dont le rôle lit le témoin. `marker_junction_readout` conserve celui-ci.

Le pont complet relie `CircularRequirement P` aux nouveaux rôles par deux retours. Pour une `ExactNonClosingRealization P history` reçue, `realizeInterior` lit la réalisation de la position du rôle. `realization_readout` retourne son accord historique concret dans `Type`, et `realization_injective` utilise la preuve d’injectivité de cette réalisation. `realizeRole` retourne `none` sur la branche finale.

Une réalisation exacte des exigences intérieures peut laisser d’autres occurrences dans l’histoire. Le pont ne transforme pas cette injectivité en exhaustivité de toutes les occurrences, ni en rigidité de toutes les réalisations.

## Conservation par transport

[CircularRoleTransport.lean](../RelationalPerimeter/Constitution/CircularRoleTransport.lean) considère une présentation construite depuis une histoire et celle de sa reconstruction par transport de signature, conservant les mêmes états et pas.

Le transport des positions compose celui de l’épine avec la réindexation par `transport_deploy`. Les rôles intérieurs ont deux retours exacts, et leur position et paquet de lien sont conservés par les applications correspondantes. Source et cible sont les nœuds transportés, avec leurs données relationnelles.

La branche finale utilise le `circularBoundaryTransport` du lot 3. Jonction, source, cible, différence et provenance choisies ont leurs accords explicites. L’assemblage des deux branches donne un transport exact de `CircularRole` ; il conserve leurs constructeurs.

Deux carrés commutent point par point :

```text
classify (transport role) = Sum.map transportPosition id (classify role)
generatedPosition (transport role) = Option.map transportPosition (generatedPosition role)
```

La classification conserve donc sa lecture intérieure/finale et la branche finale reste sans position engendrée. Aucun transport des pôles ou de l’obstruction, ni comparaison de formations cibles arbitraires, n’est ajouté ici.

## Modèles et limites

[CircularRolesExamples.lean](../RelationalPerimeter/Constitution/CircularRolesExamples.lean) teste une forme de frontière vide construite avant tout choix : aucun pointage et rôle final sur un pointage ne peuvent exister. Deux présentations ayant la même forme de frontière mais des jonctions `false` et `true` possèdent chacune un rôle final unique ; les témoins de ces rôles restent distincts.

Le même fichier ajoute un rôle extérieur dans `CircularRole P ⊕ Unit`. Ce rôle n’est l’image d’aucun rôle de la grammaire initiale ; la classification exhaustive de `CircularRole P` reste vraie. Ainsi, exhaustivité relative et possibilité d’étendre la grammaire sont compatibles.

[CircularRoleTransportExamples.lean](../RelationalPerimeter/Constitution/CircularRoleTransportExamples.lean) vérifie des rôles intérieurs distincts lisant le même lien, l’échange des témoins et provenances `Bool`, les deux retours et la conservation des branches et des carrés de classification.

La minimalité universelle de la signature et la rigidité des réalisations restent ouvertes. Le résultat fournit une grammaire précise et ses accords, pas une propriété universelle de tous les systèmes de rôles.

## Validation et livraison

Les cinq modules nouveaux comportent **109 déclarations auditées sans axiomes**. Les imports publics passent ; `lake build` réussit avec 121 tâches et `scripts/verify.ps1` vérifie 124 fichiers Lean. La [relecture indépendante](../research/agents/referee-circular-roles/report.md) conserve ses propres modèles et 49 sondes sans axiomes. Les résultats restent T2, avec vérification humaine en attente.

La livraison Git est demandée sur `codex/positive-circular-foundations`. Le snapshot du lot 4 fige les sources relues avant le commit, en normalisant uniquement CRLF vers LF pour suivre le stockage Git. Après commit, la vérification exige la même branche, une révision descendante de la base relue et toutes les mêmes empreintes ; `snapshot.py --verify-tree HEAD` contrôle aussi les fichiers réellement committés. Une modification d’une source couverte demande une nouvelle revue.
