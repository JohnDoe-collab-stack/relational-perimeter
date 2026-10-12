# Applications contrôlées des transports et des affectations

Cette tranche de D2 ouvre les invocations que la
[tranche précédente](controle-evaluation-frontiere.fr.md) conservait comme
primitives complexes. La voie étendue applique maintenant les transports
produits et interroge leur affectation par des sous-calculs contrôlés, avec
des bornes locales démontrées. Elle conserve les mêmes résultats originaux
entiers, leurs occurrences et leurs lois d'acceptation.

Elle suit le [plan v0.3](RP_ALIGN_PERSIST_SPEC_v0_3.fr.md), avec priorité A
avant B. La formation d'une fonction, son application et la requête de
l'affectation résultante sont distinguées et comptées séparément dans le
modèle de contrôle déclaré.

## La chaîne effectivement exécutée

`ControlMaster.executableSearchCode` produit la tête et les contrôles de
sources, puis une seule ouverture. Cette ouverture contient son paquet
original entier et sa préservation exécutable. Les deux enfants réellement
produits indexent le splitter et les applications qui les consomment.

La normalisation reçoit cette même frontière. `ControlStageExecution.code`
évalue le code réellement conservé par sa réduction, puis compose les
exécutants retournés avec celui de l'ouverture reçue. `ExecutableStage`
conserve le `Search` original et ce payload, avec l'accord à
`stage.preservation`. Il ne reconstruit ni l'ouverture ni la normalisation.

`expandedRunCode` consomme cette enveloppe. `executedDecideCode` obtient le
Seed original et son lecteur, applique le transport avant à la continuation
effective, puis transmet ensemble `Applied.continuation` et `Applied.reader`
à `executedCompleteCode`. La réponse payée du lecteur alimente
`candidateFromBit`, l'extraction réelle et `completionFromParts`. Le résultat
est certifié égal à la `Decision`, puis au `Dossier.Step` originaux entiers.

La formation du routage précède maintenant la décision, y compris sur refus.
Sur refus, aucun transport ni lecteur d'affectation n'est appliqué. Les
primitives `citationRouting` et `citationAssignment` des APIs historiques
n'apparaissent plus dans cette voie effective.

## Les données et les hypothèses conservées

[`Reader`](../../Tests/LocalAlignment/DocumentaryControlAssignmentApplication.lean)
est indexé par une affectation. Chaque requête produit un
`Actual (assignment query)` et possède une borne `queryBound query` accompagnée
de son `Within`. L'égalité est point par point ; aucune égalité extensionnelle
de fonctions n'est utilisée.

Une affectation arbitraire reçue exige ce lecteur exécutable en entrée.
Le maître ferme cette hypothèse :
[`ControlSeedApplication`](../../Tests/LocalAlignment/DocumentaryControlSeedApplication.lean)
produit les mêmes affectations constantes que le Seed original et leurs
lecteurs payés. Les lecteurs de flips sont ensuite formés à partir des
lecteurs effectivement reçus ; leurs requêtes invoquent le sous-lecteur réel.

[`ExecutablePreservation`](../../Tests/LocalAlignment/DocumentaryControlFrontierApplication.lean)
conserve la préservation originale entière, ses exécutants avant et arrière,
leurs coûts, les plafonds des lecteurs retournés et leurs preuves `Within`.
Chaque application produit un `Actual` de la continuation entière attendue,
le lecteur de son affectation et le respect du plafond. Les bornes utilisent
ces données reçues ; elles n'appliquent pas une map native pour découvrir
leur budget.

Les six constructeurs du code de routage SAT original sont traités. Le
préfixage conserve directement le lecteur de tête et applique l'enfant sur
la queue. La composition avant consomme le premier résultat puis le second,
avec le lecteur retourné par le premier. La composition arrière exécute le
second puis le premier. Les plafonds suivent ce même ordre.

Le retour d'une absorption est l'inclusion originale. Il conserve le lecteur
de l'occurrence retenue et ne défait aucun flip. Deux absorptions successives
peuvent ainsi conserver deux étapes de constitution dans le lecteur, même
quand sa réponse retrouve la valeur initiale. Les positions sources ne sont
pas identifiées pour obtenir le regroupement.

## Bornes locales démontrées

Pour un lecteur reçu `R`, une requête `q` et la variable de flip `s` :

- Une requête constante coûte 1 ; former son lecteur coûte 3.
- Former le lecteur d'un flip coûte 3. Sa requête possède la borne
  `R.queryBound q + q + 3` et paie la comparaison naturelle ainsi que la
  requête du sous-lecteur.
- Si `R.queryBound s ≤ b`, le lecteur retourné par un flip respecte le
  plafond `s + b + 3` à la variable sélectionnée.
- L'application structurelle d'un flip forme la continuation originale et
  son lecteur en 5 transitions.

| Application | Borne avant | Borne arrière |
|---|---:|---:|
| Identité | 2 | 2 |
| Permutation des deux premières positions | 3 | 3 |
| Absorption de la première dans la seconde | 7 | 2 |
| Absorption de la seconde dans la première | 8 | 2 |
| Expansion exacte de la tête | `b + 4` | 4 |
| Préfixage | coût enfant + 2 | coût enfant + 2 |
| Composition | coûts des deux enfants + 2 | coûts des deux enfants + 2 |

Ces bornes sont uniformes ; les chemins qui évitent un enfant ou un flip
peuvent coûter moins. Dans une composition, le coût du second exécutant est
évalué au plafond réellement propagé par le premier. Le plafond d'un
préfixage est le maximum du plafond initial et de celui de l'enfant. Les
deux lois de majoration de ce maximum sont démontrées constructivement.

La formation exécutable d'un nœud de routage coûte 9 pour identité,
permutation, préfixage et composition ; une absorption coûte 12. Les coûts
des enfants s'ajoutent. Le Stage ajoute 8 à la formation du code reçu. Le
Seed possède une borne 6 ; son cas bloqué coûte exactement 2.

`executedCompleteBound` ajoute la borne de la requête sélectionnée au
`pairBound` des deux sources reçues. `executedDecideBound` combine la borne
du Seed, le coût de l'application avant, le plafond du lecteur retourné et
ce même `pairBound`. Il ne calcule ni verdict de Seed ni transport natif
pour établir sa majoration. La recherche du maître possède ici sa finitude
constructive ; l'enveloppe globale calculable reste une obligation de D3.

## Vérification indépendante et supervision

L'agent a implémenté neuf modules Lean et les raccords de Completion/Master.
La revue principale a relu les énoncés, les motifs dépendants, les vrais
sous-paquets, les calculs de bornes et les chemins compilés. Les sondes et
les gardes ont été écrits séparément de son implémentation.

Les contrôles indépendants passent :

- 56 requêtes d'affectation, couvrant les constantes, les flips répétés et
  mélangés, les variables sélectionnées et les grandes requêtes ; six
  observations supplémentaires de lecteurs effectivement formés.
- 23 contrôles des applications : 34 paires avant/arrière, les six
  constructeurs, deux absorptions successives, les deux enfants du split,
  les ouvertures fraîches et gardées, les quatre Seed et trois décisions
  du maître réel. Les réponses viennent des lecteurs retournés.
- Carburant exact, insuffisant et excédentaire ; bornes uniformes ; positions,
  valeurs, ordre des traces et comptes locaux attendus fixés avant exécution.
  Le coût exact total du maître n'est pas inféré comme une nouvelle enveloppe
  globale à partir de ces essais.
- Les 31 contrôles d'intégration conservent leurs critères de livraison,
  d'origine, de refus, de progression, d'oubli, de reset et de rechargement.
  Leurs seuls comptes attendus changent pour les opérations nouvellement
  ouvertes : 44 formations de ressources sur les citations admissibles de
  ces fixtures, 35 sur leur refus fixé, avec zéro application sur ce refus.
- 802 audits explicites dans 59 modules de contrôle, dont 99 nouveaux noms,
  sont sans axiome. Les clients nouveaux comptent 9 et 31 audits propres.

Les gardes C vérifient les directions du payload, l'ordre de composition,
le sous-lecteur réel, les enfants réellement produits, la même ouverture
et la même réduction, puis leur consommation unique par le maître. Les
mutations modifient les entrées textuelles des gardes ; elles ne constituent
pas des exécutions de binaires corrompus. Le Code partagé des deux lecteurs
constants faux possède un initializer nommé explicitement contrôlé.

L'affectation fonctionnelle ordinaire reste disponible dans le paquet
original. Ses lectures natives sont une frontière de readout ; la voie
effective contrôlée interroge le lecteur associé. Les gardes ne prétendent
pas qualifier tous les objets statiques, tous les wrappers ni le coût
physique transitif du compilateur et de son runtime.

Les échecs de développement sont conservés dans les journaux bruts.
Les preuves intermédiaires introduisant `propext` ou `Quot.sound` ont été
rejetées, puis remplacées sans changer les énoncés ni les bornes. Les
corrections des clients sont enregistrées avant leurs nouvelles exécutions,
avec la distinction entre une nouvelle formation et un lecteur conservé,
et les dérivations des attentes corrigées. Aucun échec n'est compté comme
une validation.

La gate complète réussit sur 358 fichiers Lean, 357 modules et 28 376
constantes, avec aucune exception pour une déclaration écrite. Les 23
fixtures d'échec attendu échouent aux sites et diagnostics prévus. Les deux
nouvelles gardes rejettent respectivement 137 et 8 426 mutations textuelles ;
les gardes et sondes historiques passent également. La
[qualification](controle-application-transports-verification.json) conserve
les 436 empreintes de sources et scripts figées avant la gate, inchangées
jusqu'à sa sortie, les protocoles et les journaux bruts. Les qualifications
précédentes restent historiques.

## État du plan

L'obligation demandée — applications des transports et requêtes de leurs
affectations — est traitée dans ce cadre formel. Les sources fondationnelles,
les contrats, les quantifications, le registre et la spécification v0.3
restent inchangés. Les définitions historiques de Completion et de recherche
ont été comparées octet pour octet à la base `f89a93f` ; seule la voie
`expandedRunCode` et sa preuve de finitude consomment la nouvelle enveloppe.

D2 reste ouvert pour le calcul payé et le bootstrap des majorants, les
autres indices exécutables, les frames, recettes et codecs, ainsi que
l'administration, la composition de contrôle, les traces et les allocations
complètes. D3 doit encore former les enveloppes globales et les réserves de
successeur. D4 doit raccorder le secours commun borné au présent effectivement
conservé et rechargé ; `RecoveryData.prepare` utilise encore `Memory.step`
nativement. Les tests existants de restauration ne remplacent pas ce raccord.

La prochaine obligation concrète est d'ouvrir le bootstrap des bornes de
lecteurs et de transports, puis de poursuivre les obligations restantes de
D2 avant D3 et D4. A conserve sa priorité sur B.
