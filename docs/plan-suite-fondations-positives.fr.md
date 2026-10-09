# Plan de poursuite des fondations positives

Préparé le 9 octobre 2026 sur `codex/positive-circular-foundations`, à partir de l’arbre de travail basé sur `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685`. Ce plan décrit les sources relues avant leur livraison Git demandée. Les lots 1, 2, 3 et 4 sont réalisés dans les périmètres décrits ci-dessous ; les autres interfaces et théorèmes proposés restent des travaux à venir.

## 1. Objectif et état de départ

Construire progressivement la frontière avant le choix de sa jonction, la génération positive, les transports des familles relationnelles complètes et la classification des rôles équipés. Chaque étape doit préciser les données reçues, les données construites et les témoins conservés.

Le socle actuellement vérifié comprend :

- `PositiveCircularPresentation`, séparée des lectures de pôles et de l’obstruction ;
- le pont exact vers `CircularPresentation`, avec quatre lois de retour ;
- `ConstitutiveBoundary` et ses transports sur cinq porteurs sélectionnés ;
- un rôle final équipé, habité et unique pour une frontière déjà munie d’une jonction ;
- des modèles séparant bijection de porteurs, conservation de jonction et conservation de provenance.

Avant le lot 1, le build complet avait réussi avec 104 tâches et `scripts/verify.ps1` avait contrôlé 107 fichiers Lean. Après le lot 1, les contrôles réussissent avec 106 tâches et 109 fichiers ; après le lot 2, avec 109 tâches et 112 fichiers ; après le lot 3, avec 116 tâches et 119 fichiers ; après le lot 4, avec 121 tâches et 124 fichiers. Les revues IA indépendantes acceptent ces constructions dans leur portée annoncée ; la vérification humaine reste en attente. Ces contrôles ne certifient pas les constructions ultérieures.

**Lot 1 réalisé :** [frontière avant le choix de la jonction](frontiere-sans-jonction-choisie.fr.md), enrichissement exact, existence dans `Prop`, rôle unique par choix et modèles vide/`Unit`/`Bool`. [Relecture indépendante](../research/agents/referee-closing-boundary/report.md).

**Lot 2 réalisé :** [formation et génération positives](formation-et-generation-positives.fr.md), déploiement construit, positions et compatibilités exactes, composition réindexée, clôture conditionnelle et pont historique. [Relecture indépendante](../research/agents/referee-positive-generation/report.md). La formation reçoit ses primitives et pas admissibles ; le déploiement ne reconstruit pas toutes les données de `Step`.

**Lot 3 réalisé :** [transports de signature et de formation](transports-signature-et-formation.fr.md), toutes les fibres, calcul dépendant, restriction sélectionnée, épines et formation reconstruite conservant les mêmes états et pas, histoires exactes, composition/déploiement, ordre et clôture. [Relecture indépendante](../research/agents/referee-signature-transport/report.md). Les formations cibles arbitraires et le transport des pôles et de l’obstruction restent ouverts.

**Lot 4 réalisé :** [classification relative des rôles équipés](classification-roles-equipes.fr.md), grammaire intérieure/finale, lectures exactes, absence de position finale supplémentaire, pont historique et réalisation reçue, transports des branches et classification commutante. [Relecture indépendante](../research/agents/referee-circular-roles/report.md). Exhaustivité relative à la grammaire ; minimalité universelle et rigidité ouvertes.

Références de travail :

- [Extension positive et transports actuels](circularite-positive-et-transports-frontiere.fr.md).
- [Carte des résultats et questions](../labyrinth/FONDATIONS.fr.md).
- [Rapport du referee et limites](../research/agents/referee-positive-foundations/report.md).
- [Plan général historique](plan-reconstruction-fondations-relationnelles.fr.md), conservé comme référence dont les propositions doivent être confrontées aux sources actuelles.

## 2. Ordre d’exécution

| Lot | Résultat recherché | Dépendances | Question Labyrinth |
|---|---|---|---|
| 0 | Figer le socle et ses preuves de validation | Extension actuelle | Provenance de la carte |
| 1 — réalisé | Frontière sans jonction choisie, puis enrichissement par un témoin | Primitives et frontière actuelle | `q.equipped-final-role` |
| 2 — réalisé | Formation et déploiement positifs indépendants de l’obstruction | Primitives ; lot 1 pour distinguer chaîne et clôture | `q.positive-generation` |
| 3A — réalisé | Transport de toutes les fibres de compatibilité et de provenance | Lot 1, `ExactTypeTransport` | `q.rich-transport` |
| 3B — réalisé | Transport du déploiement et des opérations de formation reconstruite | Lots 2 et 3A | `q.rich-transport` |
| 4 — réalisé | Classification relative des rôles intérieurs et finals équipés | Lots 1 et 2 ; lot 3 pour la conservation | `q.equipped-final-role` |
| 5 — appliqué aux lots réalisés | Intégration publique et consolidation de la carte | Lots validés séparément | Résultats correspondants |

Les lots 1 à 4 sont achevés dans leurs signatures déclarées et disposent de leur intégration et validation. La livraison Git est autorisée après ces contrôles. Les questions de la section 9 et les accords entre formations arbitraires demandent des extensions propres.

## 3. Lot 0 — Figer le socle

Conserver les sources, journaux et rapports de l’extension actuelle comme référence. Préparer un commit dédié aux changements autorisés, en distinguant les fichiers locaux préexistants. Ne pas mélanger une nouvelle construction mathématique avec le déplacement de preuves déjà validées.

Lors d’une nouvelle itération, archiver la carte et le snapshot précédents, puis consigner la branche, la révision de base et les empreintes de l’arbre de travail. Les statuts de revue doivent rester associés aux énoncés effectivement relus.

**Sortie attendue :** référence reproductible du socle, avec le pont historique et les consommateurs existants vérifiés.

## 4. Lot 1 — Frontière avant le choix de la jonction

### Construction réalisée

Le module `RelationalPerimeter/Constitution/ClosingBoundary.lean` définit :

- `ClosingBoundaryShape` : sortes primitives, familles relationnelles, source et cible fermantes, différence et provenance initiales ;
- `ClosingWitness B` : fibre `B.Compatible B.source B.target`, éventuellement vide ;
- `PointedClosingBoundary` : forme de frontière équipée d’un témoin de cette fibre.

Ici, « sans jonction choisie » concerne seulement le témoin fermant : la source, la cible et les données initiales restent sélectionnées. La séparation de la provenance en une autre couche serait une décision supplémentaire, à justifier par un résultat propre.

Définir l’oubli de la jonction de `ConstitutiveBoundary`, puis la reconstruction depuis sa forme et un témoin. Prouver les retours sur les données et sur la frontière actuelle. Préserver la signature publique actuelle pendant cette construction.

### Obligations de preuve

1. Un témoin concret permet de construire l’enrichissement pointé.
2. L’existence propositionnelle d’un enrichissement correspond à l’habitation de la fibre fermante.
3. Une fibre vide interdit cet enrichissement.
4. Une fois la jonction choisie, le rôle équipé qui lui est exactement accordé est habité et unique.
5. L’unicité de ce rôle ne force pas l’unicité de tous les témoins de la fibre.

Conserver la distinction entre `Nonempty` dans `Prop` et un témoin disponible dans `Type`. Une preuve d’existence ne doit pas être utilisée pour extraire arbitrairement une jonction sans donnée constructive supplémentaire.

### Modèles séparateurs

- Fibre fermante vide : aucune frontière pointée ne peut être construite.
- Fibre `Unit` : une jonction disponible.
- Fibre `Bool` : deux jonctions distinctes sur la même forme de frontière ; chaque choix a son propre rôle équipé unique.

**Critère de clôture :** retours exacts vers `ConstitutiveBoundary`, trois modèles compilés et revue des distinctions existence/choix/unicité. La minimalité universelle de la signature n’est pas annoncée.

## 5. Lot 2 — Formation et génération positives

### Construction réalisée

`PositiveGeneration.lean` définit `PositiveFormation`, ses pas admissibles et leurs témoins de compatibilité, puis `PositiveHistory`, son déploiement et ses positions. La construction ne reçoit pas une obstruction de contraction.

Construire ensuite une histoire finie composable de ces pas et son déploiement dans `PerimeterSpine`. Distinguer l’histoire générale d’une éventuelle continuation canonique choisie. Si plusieurs successeurs sont admis, ne pas supposer qu’ils sont égaux.

La clôture doit constituer une étape explicite : une chaîne positive et un témoin fermant compatible permettent de construire `PositiveCircularPresentation`. La positivité de la chaîne ne suffit pas, à elle seule, à produire ce témoin.

### Obligations de preuve

1. Le déploiement conserve le nœud initial, le nœud terminal et les témoins de compatibilité de chaque pas.
2. Une histoire comportant un pas fournit une position non fermante ; l’histoire vide reste distinguée.
3. La composition des histoires se raccorde à la composition de leurs déploiements.
4. L’ajout d’un témoin fermant construit la présentation positive avec ses données exactes.
5. L’ajout ultérieur des lectures de pôles et de l’obstruction retrouve l’interface historique par le pont existant.

### Modèles séparateurs

- Une chaîne positive pour laquelle la fibre fermante est vide : génération disponible, clôture indisponible.
- Une chaîne équipée d’une jonction : construction d’une présentation positive.
- Deux pas admissibles vers des successeurs distincts : aucune détermination générale par le seul curseur.
- Un retour de valeur brute : vérifier qu’il n’identifie pas les occurrences portées par deux positions distinctes.

**Critère de clôture :** déploiement construit depuis les pas, accords explicites et raccord historique vérifié. Le résultat porte sur l’algèbre définie ; il n’engendre pas les sortes primitives elles-mêmes.

**Statut : réalisé et relu.** Les histoires gardent les pas entiers, tandis que l’épine conserve leurs lectures de compatibilité. La composition comporte sa réindexation terminale. Un retour à un même état brut est permis par cette interface générale ; le non-retour du générateur historique strict n’est pas exporté comme propriété de toute histoire positive.

## 6. Lot 3 — Transports de la constitution relationnelle

### 3A. Familles complètes

`SignatureTransport.lean` définit `ConstitutiveSignatureTransport`. Elle comprend les transports exacts des sortes explicite, implicite et différence, puis, pour chaque paire d’indices et chaque différence, les transports de fibres correspondants :

```text
Compatible₁ i e  ↔  Compatible₂ (mapImplicit i) (mapExplicit e)
Provenance₁ d    ↔  Provenance₂ (mapDifference d)
```

Conserver séparément les accords des données sélectionnées : indices initiaux et fermants, jonction choisie et provenance choisie. Le transport de toute une famille ne garantit pas que son application envoie un témoin distingué sur celui choisi dans la présentation cible.

Prouver identité, inversion, composition et lois de retour point par point, avec les réindexations dépendantes nécessaires. Les transports le long d’égalités doivent être explicites dans les énoncés ; aucune égalité globale de fonctions n’est requise par défaut.

Dériver le `BoundaryTransport` actuel par restriction aux indices sélectionnés, lorsque leurs accords et ceux des témoins sont fournis. Prouver que les applications obtenues et leurs retours sont bien ceux de cette restriction.

**Modèles requis :** échange de jonction, échange de provenance, et deux signatures ayant les mêmes sortes mais une fibre relationnelle habitée dans l’une et vide dans l’autre. Une bijection des sortes ne peut alors fournir le transport exact de toutes les fibres.

**Statut : réalisé et relu.** Calcul dépendant, réindexations, retours d’inversion, unités gauche/droite, associativité et restriction équipée sont compilés. Les trois modèles séparent exactitude des sortes, des familles et des témoins sélectionnés.

### 3B. Formation, épines et histoires

`SpineTransport.lean` transporte les nœuds et épines. `FormationTransport.lean` reconstruit une formation dans la signature cible en conservant les mêmes états et les pas entiers. Le transport/restauration des histoires par récursion a deux retours exacts et commute avec le déploiement et la composition. Les lectures relationnelles des pas sont transportées par les fibres complètes.

Les positions d’une épine source fixée et celles de son image ont deux retours exacts. La précédence et la succession immédiate sont conservées et réfléchies, sur l’épine et sur les positions des histoires déployées. `ClosingTransport.lean` raccorde aussi la fibre fermante et la frontière équipée d’une présentation positive.

**Statut : réalisé et relu dans cette reconstruction.** Les constructions et transports commutent point par point. Aucun transport vers une formation cible arbitraire ni équivalence générale des types d’épines n’est annoncé. Le transport des fonctions de pôles et de l’obstruction reste une extension séparée tant que leurs propres accords ne sont pas définis.

## 7. Lot 4 — Classification des rôles équipés

`CircularRoles.lean` définit la grammaire des rôles : branche intérieure portée par les positions et le paquet de lien exactement lu, branche finale portée par `EquippedFinalRole` sur la frontière équipée. Les nœuds entiers, compatibilités et provenances sont lus dans la même présentation.

La classification vers positions ⊕ `Unit` et son assemblage ont deux retours exacts. `HistoricalRoleBridge.lean` raccorde `FinalRequirement`, `CircularRequirement` et les accords d’une réalisation exacte reçue. `CircularRoleTransport.lean` conserve les branches, les données équipées et les carrés de classification sur une histoire et sa reconstruction de signature.

### Obligations de preuve

1. La classification est exhaustive relativement à la grammaire déclarée.
2. Les branches intérieure et finale sont distinguées dans cette grammaire.
3. Le rôle final ne crée pas une occurrence engendrée supplémentaire.
4. Les accords de classification lisent les témoins de la présentation et de sa réalisation.
5. Les transports du lot 3 conservent les branches et leurs données équipées.

Tester une forme de frontière sans jonction et deux choix distincts de jonction. Vérifier aussi que l’ajout d’un rôle extérieur à la grammaire ne contredit pas une exhaustivité expressément relative à celle-ci.

**Statut : réalisé et relu dans la grammaire déclarée.** Classification et raccords prouvés, sans transformer l’unicité d’un rôle équipé en rigidité de toutes les réalisations admissibles. Les modèles testent la frontière vide, les deux choix et le rôle extérieur hors grammaire. La rigidité reste `q.rigidity`.

## 8. Lot 5 — Intégration et validation

Pour chaque lot accepté :

1. Ajouter les modules validés à la façade publique et à la configuration Lake.
2. Vérifier les imports publics et les raccords historiques affectés.
3. Exécuter les modèles séparateurs utiles au changement et auditer chaque déclaration nouvelle.
4. Exécuter `lake build` puis `./scripts/verify.ps1`.
5. Relire indépendamment les énoncés, les hypothèses consommées et les limites annoncées.
6. Actualiser la carte, les ancres, la table des résultats et le journal append-only de Labyrinth.

Les preuves restent constructives selon les contrôles du dépôt. Les résultats formalisés restent T2 ; une revue IA et une vérification humaine doivent conserver leurs provenances distinctes. Une interface proposée ne devient pas un résultat établi par sa seule présence dans ce plan.

Avant d’étendre les consommateurs computationnels, établir un raccord explicite de leur interface actuelle vers la nouvelle. Une migration large fait l’objet d’un lot dédié après validation des raccords.

## 9. Travaux ultérieurs et décisions de portée

Les chantiers suivants restent recensés, mais ne conditionnent pas la clôture des quatre constructions principales :

- rigidité des réalisations admissibles : `q.rigidity` ;
- tournant couplé dans une génération à plusieurs successeurs : `q.multiple-generation` ;
- quantité structurelle générale : `q.quantity` ;
- reconstruction d’une trace en histoire composable : `q.converse-traces` ;
- fidélité des cibles après interprétation : `q.concrete-faithfulness`.

Le modèle à deux successeurs du lot 2 prépare la question générale du tournant ; il ne la résout pas. De même, le transport de signature du lot 3 prépare une comparaison de quantités sans constituer, à lui seul, leur théorie générale.

## 10. Première tranche — achevée

- [x] Construire `ClosingBoundaryShape` et la fibre fermante sans témoin choisi.
- [x] Définir l’enrichissement par une jonction et ses projections.
- [x] Prouver les retours vers la frontière actuelle.
- [x] Compiler les modèles vide, `Unit` et `Bool`.
- [x] Distinguer formellement existence, choix de jonction et unicité du rôle équipé.
- [x] Faire relire ce lot, exécuter les contrôles et consigner sa portée avant le lot suivant.

Cette première tranche fournit le cadre permettant de traiter ensuite la génération et les transports sans supposer dès le départ la jonction dont on veut étudier la constitution.

## 11. Deuxième tranche — achevée

- [x] Définir la formation sans obstruction et les histoires composables.
- [x] Construire le déploiement et ses accords de nœuds et de compatibilités.
- [x] Prouver la composition avec sa réindexation terminale explicite.
- [x] Fournir les retours exacts entre occurrences et positions non fermantes ; distinguer l’histoire vide.
- [x] Ajouter une jonction explicite pour fermer une histoire positive, puis les couches historiques reçues.
- [x] Compiler les quatre modèles et faire relire les obligations et limites du lot.

Cette tranche fournit les histoires utilisées par les transports du lot 3 réalisé ci-dessous.

## 12. Troisième tranche — achevée

- [x] Transporter toutes les fibres de compatibilité et de provenance sur leurs indices transportés.
- [x] Prouver réindexations, unités, associativité et retours d’inversion point par point.
- [x] Restreindre aux frontières équipées avec accords des cinq données choisies.
- [x] Transporter épines, positions, précédence et succession immédiate.
- [x] Reconstruire la formation avec états et pas entiers conservés ; histoires et occurrences avec retours exacts.
- [x] Raccorder composition, déploiement, liens, continuation choisie et clôture.
- [x] Compiler les modèles séparateurs, les imports publics et les contrôles, puis faire relire le périmètre.

Cette tranche fournit les transports utilisés par le lot 4 réalisé ci-dessous.

## 13. Quatrième tranche — achevée

- [x] Définir les rôles intérieurs avec position et lien exactement lu, puis la branche finale équipée.
- [x] Classifier et assembler avec deux retours ; séparer les branches et la position engendrée de la clôture.
- [x] Raccorder les marqueurs historiques et les accords d’une réalisation reçue.
- [x] Transporter les données des rôles, conserver les branches et faire commuter classification et lecture des positions.
- [x] Compiler les modèles vide, deux choix, rôle extérieur et nœuds répétés ; vérifier imports et dépôt.
- [x] Faire relire les sources, les documents et la carte ; préparer la livraison Git autorisée.

Les quatre constructions principales sont réalisées. La rigidité, la minimalité universelle, les formations cibles arbitraires, les pôles et l’obstruction restent ouverts.
