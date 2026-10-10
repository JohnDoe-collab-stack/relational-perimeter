# Contrôle documentaire instrumenté : évaluateur et premier raccord

Ce document décrit le premier passage de développement, identifié par son
relevé et ses empreintes. Le [passage suivant](controle-permissions-documentaires.fr.md)
ouvre désormais la recherche de permission et le calcul de position ; ses
seuils et résultats de vérification sont consignés séparément. Les descriptions
du raccord et les comptes ci-dessous se rapportent au premier passage.

Cet incrément applique D2 du [plan v0.3](RP_ALIGN_PERSIST_SPEC_v0_3.fr.md),
après le raccord de reprise D1. Il ajoute un évaluateur à carburant, démontre
sa correction, sa complétude et sa monotonie, puis l'emploie pour lire les
liaisons retenues et produire une étape documentaire. Il travaille depuis
la révision `e291dc0d2b45880078e9c4a3b85aa0ab175bdf71`, sur la branche
`codex/align-persist-recovery` isolée. A conserve la priorité sur B.

La portée obtenue est précise : chaque cellule de liaison visitée est payée,
les valeurs ainsi lues alimentent les producteurs reçus, et le certificat
consomme leur paquet effectif. Le coût interne des producteurs et des
fonctions d'assemblage reste à instrumenter. D2 entier, D3, CONT-03 et P15
restent ouverts à cette frontière ; cet incrément ne les déclare pas clos.

## Convention d'évaluation et lois démontrées

[DocumentaryControlInterpreter](../../Tests/LocalAlignment/DocumentaryControlInterpreter.lean)
définit un programme dont chaque transition porte une étiquette et une
continuation différée. Une transition coûte une unité. Rendre un résultat
déjà calculé coûte zéro. Avec zéro unité, une transition ne lance pas sa
continuation. Le dernier passage vers un résultat est payé selon la même
convention que les autres transitions.

`execute` produit ensemble la valeur, la liste des transitions et une trace
typée de cette évaluation. La borne porte sur la longueur de cette liste.
`runCtl` expose la valeur et cette liste. Le carburant n'entre pas dans les
arguments des continuations : il permet ou interdit leur exécution.

| Obligation | Déclaration et conclusion |
| --- | --- |
| CTL-SOUND | `ctl_sound` : chaque résultat de `runCtl` possède une trace du même programme, de la même valeur et des mêmes étiquettes, dont la longueur ne dépasse pas le carburant |
| CTL-COMPLETE | `ctl_complete` : toute trace finie est atteinte à tout carburant supérieur ou égal à sa longueur |
| CTL-MONO | `ctl_mono` : un résultat atteint reste exactement le même avec davantage de carburant, étiquettes comprises |
| Déterminisme | `Eval.unique` : deux traces du même programme ont la même valeur et les mêmes étiquettes |
| Seuil exact | `fuel_required` et `fuel_short` : le coût d'une trace connue est nécessaire ; en dessous, aucun résultat n'est rendu |
| Composition | `Code.bind` et `Eval.bind` : le résultat effectif du premier calcul alimente le suivant ; leurs listes de transitions se concatènent |

Ces lois quantifient sur les programmes et traces de l'évaluateur. Elles
ne supposent pas la réussite du programme documentaire. `Result.sound`
est le certificat exécutable : il projette la trace déjà stockée, sans
recalculer le programme pour la retrouver. La complétude logique ne sert
pas à extraire un programme depuis une existence ; le programme et son
évaluateur sont définis séparément et calculables.

## Lecture payée du présent constitué

[DocumentaryControlBindings](../../Tests/LocalAlignment/DocumentaryControlBindings.lean)
parcourt la table finie réellement conservée par `Snapshot.FrameData`.
Une référence en position `p` demande exactement `p + 1` transitions de
liaison. `readTrace`, `read_within` et `read_short` établissent ce résultat
pour toute table et toute référence bien typée.

La valeur rendue est accompagnée de son égalité avec la cellule de cette
table. Elle peut être une occurrence ou une absence. La lecture conserve
l'identité de l'occurrence ; elle n'effectue pas une recherche par égalité
de valeur. Les cas distinguent notamment deux citations de valeur `42`
dont les références sont en positions `4` et `1` dans le stockage effectif.

Le calcul de la position, la capture initiale de la table et la construction
de la borne ont leur propre obligation de bootstrap. Leur coût n'est pas
inclus implicitement dans les transitions de lecture.

## Raccord aux producteurs et au certificat

[DocumentaryControlStep](../../Tests/LocalAlignment/DocumentaryControlStep.lean)
construit le programme instrumenté d'une instruction reçue. Il reçoit le
`FrameData` et l'instruction, sans certificat d'admissibilité pour choisir
son calcul.

Une citation appelle `Dossier.step` une fois, puis donne son résultat à
`Program.quotationStep`. Une déduction lit d'abord la référence gauche ;
si elle est présente, elle lit la droite. Ces occurrences effectives
alimentent `Deduction.execute`, puis `Program.deductionStep` consomme cette
décision. Une absence produit le paquet `missingStep`. Aucune branche ne
remplace les données reçues pour obtenir un résultat favorable.

Le paquet rendu porte l'égalité avec `Program.step` sur ce même cadre et
cette même instruction. Cette égalité est une preuve effacée à l'exécution :
le programme instrumenté n'appelle pas `Program.step` pour comparer deux
productions. `finite` démontre que ce programme possède une trace finie
pour toute instruction, y compris un refus ou une prémisse absente.
`sufficient_fuel` relie cette trace à l'évaluateur. Cette existence ne fournit
pas encore une enveloppe de ressources calculée depuis l'état.

`complete` reçoit le résultat effectif de l'interprète, l'admissibilité
primitive de l'instruction et la complétude du cadre initial. Il obtient
la complétude du successeur en consommant le champ de progrès de ce paquet.
Il ne lance aucun producteur. `reset_same_code` montre que l'effacement du
contexte de proposition conserve le programme instrumenté.

Les étiquettes d'entrée `quotationProducer` et `deductionProducer` comptent
actuellement des invocations. Une telle invocation peut contenir une
recherche, des lectures, des opérations sur entiers et des allocations.
Une unité d'entrée ne borne pas ce travail interne. Les assemblages et
la gestion de la trace ont aussi des coûts à fermer avant une enveloppe
complète de contrôle ou de mémoire.

## Carte des dépendances

| Passage | Dépendance conservée |
| --- | --- |
| Formation | Tables finies reçues, références typées, occurrences, cadre et instruction documentaire |
| Exécution | Lecture payée des cellules, producteurs documentaire et de déduction reçus, fonctions d'assemblage existantes |
| Preuve | Trace stockée de l'évaluateur, égalité du paquet avec l'étape reçue, admissibilité primitive et progrès de ce paquet |
| Transport | Même programme après reset ; mêmes cadres après les deux projections d'histoires réellement exécutées ; test de chargement du composant de contrôle avec maître fourni |

Le reset n'efface pas les ressources ou les liaisons constitutives. Le test
de chargement utilise le codec de contrôle existant et reçoit encore le
dossier et le stockage maître. Il ne constitue pas une reprise autonome
du maître depuis les seuls octets dans un processus neuf.

## Vérification de développement

Les [cas Lean](../../Tests/LocalAlignment/DocumentaryControlInterpreterCases.lean)
consomment les producteurs du maître public. Le certificat de la somme
établit la valeur `2` et les origines `[1, 2, 1, 2]` du résultat instrumenté.
Les instructions interdites restent représentables et produisent un refus.
Une prémisse absente produit une absence ; une instruction autorisée avec
une demande erronée conserve sa valeur réellement calculée et manque son
critère. L'admissibilité n'est pas supposée pour ces cas négatifs.

Le [client d'exécution](../../scripts/run-documentary-interpreter-smoke.py)
teste dix valeurs de carburant pour dix scénarios, soit cent verdicts,
avec neuf contrôles d'intégration supplémentaires. Les seuils, événements,
valeurs et origines attendus sont littéraux. Les scénarios couvrent la
citation, la déduction, la somme, les refus de règle et de source, l'absence
gauche ou droite, la mauvaise demande et les deux identités de même valeur.
Les contrôles supplémentaires couvrent le présent, son reset, son contrôle
chargé, les deux histoires oubliées et le certificat stocké. Les douze
audits du client sont sans axiome.

Le [contrôle du C produit](../../scripts/check-documentary-interpreter-codegen.py)
vérifie l'entrée différée après test et décrément du carburant, les deux
sites de production dont les résultats alimentent leurs assemblages, et
les deux certificats consommateurs. Douze mutations textuelles de ces
corps sont refusées : duplications, rejeux, entrée anticipée, suppression
du décrément et substitution du paquet fourni à l'assemblage. Ces fixtures
testent le contrôleur ; elles ne sont pas des exécutables mutants compilés.
La portée du contrôle est celle des corps C nommés, complétée par les gates
documentaires existantes. Il ne démontre pas une borne du graphe complet.

Les nouveaux contrôles sont intégrés aux deux scripts de vérification.
La gate complète `scripts/verify.ps1` a réussi sur **302 fichiers Lean** :
25 641 constantes dans 301 modules, 364 exceptions générées par le
compilateur, aucun axiome écrit et 23 fixtures de refus conformes. Les
65 audits explicites des quatre nouveaux modules sont sans axiome.
Les sources Lean et les empreintes des 181 modules de la chaîne de
dépendances sont restées inchangées pendant cette vérification.

Le [relevé de cet incrément](controle-instrumente-documentaire-verification.json)
consigne les empreintes et commandes. Les relevés et évidences historiques
restent attachés à leurs révisions. Aucun audit indépendant ni essai
confirmatoire de modèle local n'est attribué à cet incrément.

## Travail suivant dans l'ordre du plan

Il faut compléter D2 en instrumentant les contrôles internes et les
assemblages traversés par les producteurs reçus, avec leurs résultats
partagés. La représentation des entiers, des lecteurs, de la recherche et
de la trace doit fixer ce que compte chaque primitive ; les auxiliaires
ne doivent pas échapper au compte.

D3 devra ensuite calculer leurs bornes depuis l'état, borner ce calcul
de bootstrap, établir les enveloppes obligatoires et facultatives et leur
fermeture sur les successeurs. D4 composera ces mêmes programmes pour fermer
CONT-03 sur le secours effectivement appelé. Le chargement complet A1,
les transactions A2, leur réalisation physique A3 et la comparaison avec
Qwen A4/A5 restent après ces obligations. B conserve son ordre ultérieur.
