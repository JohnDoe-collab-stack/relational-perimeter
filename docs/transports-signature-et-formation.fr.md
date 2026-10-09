# Transports de signature et de formation

Le lot 3 transporte toutes les fibres relationnelles, puis les épines et une formation reconstruite sur les mêmes états et pas. Il conserve les positions, leur précédence et leur succession immédiate. Le [plan](plan-suite-fondations-positives.fr.md) distingue cette construction de la classification des rôles du lot 4.

## Signature complète et réindexation

[SignatureTransport.lean](../RelationalPerimeter/Constitution/SignatureTransport.lean) définit `ConstitutiveSignature` : sortes explicite, implicite et différence, famille de compatibilité, famille de provenance. `ConstitutiveSignatureTransport S T` reçoit trois transports exacts des sortes et un transport exact pour **chaque fibre**, aux indices transportés :

```text
S.Compatible i e ↔ T.Compatible (implicit.forward i) (explicit.forward e)
S.Provenance d   ↔ T.Provenance (difference.forward d)
```

Ces applications et leurs inverses sont des données concrètes. Leurs deux retours sont prouvés point par point. Les familles peuvent varier avec leurs indices, et une fibre peut être vide.

`compatibilityAt` et `provenanceAt` raccordent les images à des indices cibles nommés par égalités explicites. Dans `reverse`, une fibre cible est réindexée par les retours des sortes avant l’application inverse. Dans `compose`, le second transport de fibre est lu aux images du premier. Les unités gauche/droite et l’associativité des applications de fibres sont prouvées, ainsi que les retours d’inversion avec leurs réindexations. Aucune égalité globale de fonctions n’est nécessaire.

## Restriction aux données choisies

`restrictCarriers` reçoit les accords de source, cible et différence. Ses transports de jonction et de provenance sont exactement les transports des familles complètes, suivis de leur réindexation.

`restrict` demande en plus deux accords : l’image de la jonction choisie est la jonction cible, et l’image de la provenance choisie est la provenance cible. Il construit alors le `BoundaryTransport` du socle. L’exactitude de toutes les fibres ne détermine pas à elle seule ces choix.

[SignatureTransportExamples.lean](../RelationalPerimeter/Constitution/SignatureTransportExamples.lean) vérifie trois séparations :

- Les mêmes sortes `Bool` peuvent porter des fibres de compatibilité `Unit` ou `Empty`. Aucun transport exact des familles ne relie ces deux signatures.
- Un transport exact de toutes les fibres peut échanger la jonction tout en conservant la provenance et les indices.
- Un autre peut échanger la provenance tout en conservant la jonction.

Un modèle déplace les trois indices et les deux témoins et reçoit les cinq accords nécessaires. Sa restriction a les retours exacts attendus. D’autres lectures vérifient des fibres non sélectionnées par cette frontière.

## Épines, positions et ordre

`mapNode` est défini dans `SignatureTransport.lean` ; [SpineTransport.lean](../RelationalPerimeter/Constitution/SpineTransport.lean) construit `mapSpine` depuis ces transports. Chaque nœud garde les lectures transportées de ses cinq champs ; chaque avancée garde son témoin de compatibilité transporté.

`mapSpine_final` raccorde le nœud terminal. `mapSpine_append` raccorde la composition avec la réindexation du suffixe par ce même accord. `mapSpine_link` raccorde le paquet complet de deux nœuds et de leur compatibilité lu à une position.

Pour une **épine source fixée**, `mapPosition` et `restorePosition` donnent un transport exact entre ses positions et celles de son image. `precedes_iff` et `next_iff` préservent et reflètent séparément la précédence et la succession immédiate. Ces accords ne sont pas déduits de la seule bijection de positions : ils sont prouvés sur les constructeurs des relations.

Cette interface fournit le transport d’une épine et l’équivalence de ses positions. Elle n’emballe pas une équivalence générale entre tous les types d’épines de deux signatures.

## Formation reconstruite et histoires

[FormationTransport.lean](../RelationalPerimeter/Constitution/FormationTransport.lean) définit `F.transport change`. La formation reconstruite conserve littéralement `State` et `Step`; ses nœuds et ses lectures de compatibilité sont transportés par la signature complète.

`transportSignature` et `restoreSignature` changent l’index de formation d’une histoire par récursion. Ils conservent les états intermédiaires et **toutes les données de chaque pas**, avec deux retours exacts. La même construction donne un transport exact des occurrences.

Les opérations commutent :

```text
transport (append first second) = append (transport first) (transport second)
deploy (transport history)      = mapSpine (deploy history)
```

`transport_position` expose l’égalité de déploiement utilisée pour réindexer les positions. `transport_precedes_iff` et `transport_next_iff` conservent et reflètent les relations des positions déployées. `transport_link` conserve leurs lectures de nœuds et de compatibilité.

Une continuation déjà choisie transporte son successeur et son pas inchangés. `transport_walk` raccorde son itération à celle de la formation reconstruite. Cela ne fournit aucune continuation nouvelle et ne détermine pas un successeur unique pour toute formation.

[FormationTransportExamples.lean](../RelationalPerimeter/Constitution/FormationTransportExamples.lean) distingue deux histoires dont les pas `Bool × Bool` ont la même lecture de compatibilité et des données supplémentaires différentes. Leurs épines coïncident, mais le transport des **histoires** conserve ces données et revient exactement à chacune. Trois pas lisant le même nœud conservent leurs positions distinctes, leur ordre et leur succession après échange des témoins `Bool`.

L’équivalence d’histoires annoncée concerne cette reconstruction conservant les mêmes états et pas. Un transport vers une formation cible arbitraire demanderait ses propres accords sur états, nœuds, pas et lectures. Le déploiement seul ne reconstruit toujours pas toutes les données de `Step`.

## Clôture et frontière équipée

[ClosingTransport.lean](../RelationalPerimeter/Constitution/ClosingTransport.lean) transporte la fibre fermante de l’histoire vers celle de son image. L’accord de source provient du déploiement et du nœud terminal ; le nœud initial fournit la cible.

Un témoin reçu donne une présentation circulaire positive transportée. `circularBoundaryTransport` dérive sa frontière équipée par restriction, avec les cinq accords de données choisies. Les jonctions ont deux retours ; jonction et provenance sont conservées par les applications correspondantes. [ClosingTransportExamples.lean](../RelationalPerimeter/Constitution/ClosingTransportExamples.lean) vérifie une jonction et une provenance `Bool` échangées, le retour et le transport du rôle final actuel.

Un transport exact ne transforme pas une fibre vide en fibre habitée. Il transporte une clôture disponible ; il n’en crée pas une à partir de la positivité seule.

## Validation et suite

Les sept modules nouveaux comportent **162 déclarations auditées sans axiomes**. Les imports publics sont vérifiés. `lake build` réussit avec 116 tâches et `scripts/verify.ps1` contrôle 119 fichiers Lean. La [revue indépendante](../research/agents/referee-signature-transport/report.md) conserve ses propres modèles, les réindexations et les limites de portée. Les journaux sont dans `labyrinth/evidence/transport-*.log`. Les résultats restent T2 ; vérification humaine en attente.

Le [lot 4 est réalisé](classification-roles-equipes.fr.md) dans sa grammaire déclarée, avec classification et transports des rôles équipés. Le transport des fonctions de pôles et de l’obstruction, les accords entre formations arbitraires, la rigidité et le tournant couplé à plusieurs successeurs restent des extensions distinctes.
