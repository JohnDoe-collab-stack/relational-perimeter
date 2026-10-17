# Raccord de Gödel, du regroupement et de la complétude séquentielle relationnelle

## Statut et portée

Ce document est le passage scientifique canonique du raccord formalisé par
`RelationalPerimeter.Constitution.Godel.RelationalCompleteness`. Il décrit un
théorème constructif interne au cadre relationnel du dépôt. Il ne constitue ni
un verdict d'originalité, ni un audit indépendant, ni une identification avec
la totalité des nombres réels classiques.

Les réels relationnels considérés ici sont produits par des exécutions à
précision finie. Une famille de Cauchy exécutée, son producteur, son module
monotone et sa loi de Cauchy sont reçus. Les réponses limites, leur cohérence,
la convergence des sources admissibles et les regroupements finis sont ensuite
construits. Les codes dyadiques sont des readouts aval de ces constructions ;
ils ne constituent ni les histoires ni les occurrences.

## Conclusion formelle du raccord Gödel–regroupement–réels

Pour toute exécution gödelienne effective `execution` et toute famille de
Cauchy exécutée `family` sur la présentation exacte
`godelPerimetralPresentation execution`, à la profondeur de base `1`,
`raccord execution family` construit un unique paquet `Result`. La
quantification terminale est exactement :

```text
execution : ExecutedGodelProduction ...
family    : ProducedCompleteness.ExecutedCauchyFamily
              (godelPerimetralPresentation execution) 1

Result execution family
```

Le champ `master` de ce paquet est exactement
`CommonRealRuntime.complete family`. Il conserve le maître générique riche,
le runtime commun directement exécutable, la réalisation exacte de l'archive
riche par ce runtime, le producteur de regroupements finis et la continuation
de la cible installée. Le champ `producedReal` est le réel relationnel produit
par les pas du runtime autoritatif, et `firstRun` réutilise exactement le
premier pas limite fourni par ce producteur. Le paquet conserve aussi la
persistance des occurrences gödeliennes et rejette les deux fermetures
totalisantes spécifiées.

Une requête source contient un indice et une précision, jamais un résultat.
Une requête limite exécute la source diagonale choisie par le module, puis le
programme de regroupement qui consomme cette même production. Le code lu est
celui de l'action retenue dans la mémoire. Pour un lot fini, le caller fournit
une liste de requêtes sources admissibles, pas une cible : l'archive riche
exécute les sources dans l'ordre, construit la chaîne dépendante, la regroupe,
installe la cible produite et expose seulement ensuite son readout.

Dans le même paquet, toute `ExecutedGodelTotalLoop` fournit la conversion
`Truth(G) -> Proof(G)` rejetée par la vérité et la non-prouvabilité du même
énoncé diagonal produit. Toute `GlobalSameRegimeClosure` doit agir à partir de
sa racine et le long des `DepthExtension` reçues ; sa restriction à l'extension
canonique `0 -> 1` produit l'admission gödelienne déjà réfutée. La branche
négative ne produit aucune approximation numérique.

## Chaîne constitutive commune

La chaîne part de la production diagonale, de la vérité et de la
non-prouvabilité de `G`, puis de la présentation périmétrale `P`. Sa
continuation affirmative est `H1`. `Journal.root P 1` possède
définitionnellement cette histoire ; son type conserve simultanément `P` et la
profondeur de base. Un journal formé sur une autre présentation ne peut donc
pas être substitué.

Chaque programme exécuté imbrique, dans cet ordre, le contexte reçu, la
recherche, l'action relationnelle, la préservation séparée, l'autorisation et
la décomposition, la continuation, puis la mémoire. La recherche consomme le
contexte produit par la réception ; l'action consomme le résultat de cette
recherche ; la mémoire conserve la continuation et l'action exacte. Un témoin
rangé à côté d'une sortie, une égalité de codes ou un rejeu indépendant ne
remplacent pas cette dépendance exécutée.

Chaque phase ajoute une occurrence fraîche au journal privé. Les trois
occurrences gödeliennes antérieures sont transportées injectivement à travers
chaque phase, restent deux à deux distinctes et restent distinctes de
l'occurrence fraîche. Pour une limite, le transport du regroupement part du
transport terminal de la source possédée par la même réponse. Pour un run,
`persistThroughRunFrom` suit la trace déjà exécutée ; il ne réexécute pas les
requêtes.

Le runtime typé part à la profondeur absolue `1`. Sa première requête limite
exécute six phases sources puis six phases de regroupement : la source atteint
`H7` et la réponse limite atteint `H13`. L'état final, l'événement,
l'observation et la ressource mémorisée proviennent du même pas retenu.

## Regroupement historique et consommation de la totalité finie

`ExecutedSourceChain` impose l'ordre chronologique : chaque source fraîche
commence au journal terminé par la précédente. `ExactConsumption` reproduit
cette chaîne constructeur par constructeur. Son cas successeur conserve la
consommation exacte du préfixe et consomme la source fraîche exacte. Il est
ainsi impossible d'omettre, de dupliquer ou de remplacer une source tout en
habitant le type requis.

La normalisation historique ne repart pas d'une graine neuve. À chaque
extension, `HistoricalSeed` fournit la charge normalisée précédente.
`advanceBatch` transporte cette ressource complète par `liftBatchCharge`, puis
`normalizeFresh` exécute seulement l'obligation fraîche sur cette ressource
transportée. `BatchAdvance.resultFromTransport`, `consumed_exact` et
`oldCharge_exact` lient le résultat à ce transport : le préfixe consommé, les
anciennes charges et leurs témoins `Near` ne sont ni remis à zéro ni reconstruits
depuis le seul code. La liste `resources` archive les ressources transportées ;
`localCharges` est une archive secondaire et ne justifie pas à elle seule la
dépendance historique.

`BatchGrouping.program` construit sa `ProducedTarget` depuis cette exécution
historique. Son action possède l'`ExactConsumption`, la charge normalisée et
les regroupements locaux dérivés de cette même charge. La mémoire retient
l'action exacte. `ExecutedFiniteGrouping.normalizedBatch_consumed_length` et
`normalizedBatch_consumed_exact` établissent la consommation de toutes et
seulement les sources de la chaîne, dans l'ordre ancien-vers-récent.
`ExactIndexEnumeration` n'est qu'une projection unaire de forme ; elle n'est
pas la preuve de l'exhaustivité.

Le regroupement n'identifie pas les profils sources. Il les porte vers une
cible commune sous un contrat de proximité, tout en conservant leurs
productions, occurrences et positions chronologiques. L'égalité du readout
terminal est une projection aval, non une égalité des sources.

## Runtime vivant, archive riche et mémoire exacte

`CommonRealRuntime.Environment` contient comme données exécutables le
`SourceProducer` et le module. `CommonRealRuntime.Runtime` est un type commun,
non indexé par une famille : il contient cet environnement et la mémoire
vivante `ReducedState`, composée de la profondeur courante et de la dernière
observation installée. `performReal` lit l'environnement présent dans l'état et
exécute les requêtes `source`, `limit`, `group`, `continueInstalled` et les
refus. `runReal` enchaîne les transitions effectivement retournées.

Cette mémoire est exactement celle requise par le contrat déclaré, mais la
portée de cette exactitude est essentielle. `fixedEnvironmentMinimality`
établit, pour un environnement exécutable fixé, l'équivalence entre égalité de
la mémoire et égalité de tous les futurs finis. Il ne compare pas deux
producteurs différents en oubliant leur environnement. Pour l'archive riche
d'une famille fixée, `archiveRealization` couvre les sources brutes, limites,
lots, continuations, lectures et refus ; `archiveMemoryMinimality` caractérise
exactement sa projection commune. Ces théorèmes ne sont ni une borne de coût
physique ni une identification des ressources riches.

Le runtime autoritatif conserve séparément le journal et les paquets
d'exécution dépendants. `projectArchive` oublie ces ressources seulement après
leur exécution et conserve l'environnement comme donnée. `archiveProjection`
prouve que chaque transition riche et la transition commune ont le même état
projeté et le même événement. La priorité reste donc : exécution riche,
projection exacte, puis readout.

Un regroupement riche installe `OwnedTarget.batch grouped`, c'est-à-dire la
cible produite par son action. `continueInstalled` exige cette cible installée,
exécute `targetContinuationProgram` et relit la ressource retenue elle-même ;
il ne rappelle pas le producteur pour fabriquer une valeur indépendante. Une
requête source ultérieure efface l'installation, conformément au contrat de
futurs déclaré.

## Comportements réels et correspondance numérique

Le réel positif terminal est un comportement du runtime : depuis tout état
riche `Reachable` et pour toute précision, il produit le pas limite canonique.
Sa cohérence et la proximité des sources consomment les réponses appartenant à
ces pas et la loi de Cauchy reçue. Le témoin d'accessibilité borne le domaine du
producteur ; il n'est pas remplacé par une simple égalité de readouts.

À environnement fixé, des sources distinctes regroupées depuis des profondeurs
égales peuvent avoir la même projection et donc les mêmes futurs du contrat
d'archive. Elles ne deviennent pas la même occurrence. Entre environnements,
`NumericalFutureEquivalent` compare seulement les readouts des transitions
limites effectivement exécutées. Cette relation n'identifie ni les programmes,
ni les encodages, ni les profondeurs, ni les ressources.

La correspondance avec les présentations dyadiques effectives et le carrier de
Cauchy effectif est énoncée séparément dans
[le passage canonique de correspondance](runtime-real-cauchy-effective-correspondence.fr.md).
Elle part du runtime pour produire le readout numérique et ne reconstruit pas
une histoire riche depuis ce readout.

## Branche négative conservée

La totalité positive des requêtes finies n'est pas `P.TotalLoop`. Une boucle
totale identifie `Truth(G)` et `Proof(G)` et fournit la conversion interdite.
Son rejet consomme la vérité et la non-prouvabilité du même témoin produit.

La fermeture globale interdite fournit une admission racine, un opérateur
`extendOne` appliqué à une admission déjà constituée et la préservation des
labels antérieurs. `closeAlong` est dérivé récursivement de ces données en
consommant la `DepthExtension` reçue. Le terme final vers `Empty` consomme
l'admission à `H1` ainsi produite ; il ne lit pas directement le champ
`preservesPriorLabels`, qui appartient au contrat de formation et de transport.

Le même témoin et le même périmètre portent donc deux conclusions compatibles :
la fermeture totalisante du même régime est rejetée, tandis que tous les futurs
finis nécessaires à la complétude séquentielle relationnelle sont produits et
cohérents.

## Instance HA et limites

`RelationalPerimeter.Instances.HeytingArithmetic.RelationalCompleteness`
instancie le côté gödelien par l'exécution HA concrète du dépôt. Pour toute
famille de Cauchy exécutée sur cette présentation exacte à la base `H1`, il
construit le raccord sans ajouter d'hypothèse de vérité, de preuve ou de
fermeture. L'instance de correspondance effective reçoit, elle, la présentation
numérique ou le carrier comme donnée ; Gödel fixe son périmètre mais ne calcule
pas ses approximations.

Le résultat ne couvre pas tous les réels classiques. Il ne démontre pas la
complétude par borne supérieure, la densité, le transport de l'addition, de la
multiplication, de l'ordre ou de l'apartness, la propriété archimédienne, `AC`
ou `CH`. Il établit la complétude séquentielle effective des comportements
relationnels fournis par les familles reçues et leur exécution dans le runtime
commun, avec les limites de portée ci-dessus.
