# Raccord de Gödel, du regroupement et de la complétude séquentielle relationnelle

## Statut et portée

Ce document est le passage scientifique canonique du raccord formalisé par
`RelationalPerimeter.Constitution.Godel.RelationalCompleteness`. Il décrit un
théorème constructif interne au cadre relationnel du dépôt. Il ne constitue ni
un verdict d'originalité, ni un audit indépendant, ni une identification déjà
prouvée avec toutes les présentations usuelles des nombres réels.

Le résultat porte sur les **réels relationnels** définis ici comme des modules
effectifs de réponses à précision finie. La famille de Cauchy, son module et
ses preuves de cohérence sont des données positives reçues. La limite, ses
exécutions et sa convergence ne figurent pas dans les prémisses : elles sont
construites.

## Conclusion formelle du raccord Gödel–regroupement–réels

Pour toute exécution gödelienne effective `execution` et toute famille de
Cauchy exécutée sur l'unique présentation
`godelPerimetralPresentation execution`, il existe un réel relationnel limite,
répondant effectivement à toute précision finie, tel que tout terme placé
au-delà du module est proche de cette réponse à la précision demandée. Les
requêtes sources et les requêtes de limite sont exécutées dans la même tour
d'histoires engendrées ; leurs readouts dyadiques signés sont des projections
postérieures à l'exécution. À chaque précision, le regroupement porte les
sources retenues vers la même obligation cible sans identifier leurs identités,
et tout ajout fini prolonge les anciennes opérations par une trace effective.
Dans ce même paquet, une boucle totale ou l'admission de fermeture du premier
préfixe dérivée d'une tentative de fermeture agissant sur tous les préfixes
finis produit `Empty` par la conversion
`Truth(G) -> Proof(G)` et la non-prouvabilité du même énoncé diagonal produit.

La quantification terminale est donc :

```text
execution : ExecutedGodelProduction ...
family    : ExecutedCauchyFamily (godelPerimetralPresentation execution)

Result execution family
```

`Result` contient conjointement la correspondance gödelienne antérieure, la
complétude séquentielle effective, le producteur maître
source–regroupement–limite pour tout journal et toute précision, le producteur
de regroupement de toute chaîne finie de sources effectivement exécutées, sa
spécialisation exacte à la première production complète, la persistance des
trois occurrences de Gödel à travers les deux requêtes possédées par cette
même production, et les deux fonctions de rejet. Il ne conserve aucune
exécution parallèle reconstruite à partir du seul code de limite. La seconde rejette une
`GlobalSameRegimeClosure`; elle ne reçoit pas l'admission du premier préfixe
comme champ. La conclusion positive ne dépend pas de `Empty`; les fonctions de
rejet ne fabriquent pas la limite.

## Chaîne constitutive commune

La chaîne commence par l'exécution diagonale déjà établie : réception du
codage, diagonalisation, production de `G`, certification de sa vérité et de sa
non-prouvabilité, puis construction de la présentation `P`. Le périmètre et sa
première continuation donnent `H₀` et `H₁`.

Le journal réel n'introduit pas une seconde famille d'histoires. Son histoire à
profondeur `n` est exactement `ConstitutiveGeneration.iteratedHistory P n`.
Une requête publique est décomposée, dans cet ordre, en six opérations :

1. réception du contexte ;
2. recherche exécutée ;
3. action relationnelle ;
4. autorisation et décomposition ;
5. continuation effective ;
6. mémoire sous contrat.

Chaque opération ajoute l'occurrence fraîche réelle du producteur libre. Le
readout vient ensuite et n'ajoute aucune occurrence. La graine utilisée par le
raccord a exactement pour histoire `H₁`; après une requête complète, l'histoire
est `H₇`. Le programme maître exécute deux requêtes successives — la source
diagonale puis la limite alimentée par le regroupement — et atteint exactement
`H₁₃`. Les occurrences de production, de certification et de continuation de
Gödel sont transportées d'abord par l'extension exacte du journal de la
requête source possédée, puis par celle de la requête de limite possédée.
L'injectivité du transport conserve leurs trois distinctions, et l'obstruction
terminale reste celle de `P`.

## Ce que regroupe le regroupement

À une précision fixée, une source est constituée d'un indice de terme, d'une
précision de lecture, d'un témoin que l'indice dépasse le module et d'un témoin
que la lecture raffine la précision demandée. Le profil présenté au
regroupement ajoute le journal et le paquet d'exécution effectif de cette
source. Son code est projeté de ce paquet ; sa provenance contient la requête,
l'occurrence de réception, l'occurrence de mémoire produite et la trace des six
phases. La cible est la réponse diagonale construite : le terme d'indice
`modulus p`, lu à la précision `p`.

Le regroupement ne fusionne pas les sources. Ses états sont soit une source
avec son identité, soit la cible commune. L'unique pas autorisé d'une source
vers la cible consomme une charge portant le readout de l'exécution possédée,
sa relation exacte au profil et le témoin positif `Near` vers la cible. La
sortie conserve explicitement le code source et ce même témoin consommés, puis
retourne exactement le code cible. Une preuve séparée établit l'admission de
cette sortie dans l'état cible. Deux sources distinctes restent des états
distincts, même lorsque `carry` les place dans la même image normale. Le
readout de la limite est prouvé égal à la sortie de cette action, et non à une
reconstruction parallèle.

Une sélection finie est un préfixe positif d'identités prises dans une enveloppe
globale fixée. `ExecutedSourceChain` ne reçoit pas une liste arbitraire de
valeurs : il enchaîne chronologiquement les paquets d'exécution, et chaque
nouvelle source commence dans le journal exactement terminé par la précédente.
La sélection finie est dérivée de ces seules exécutions possédées.

Le regroupement de lot part de l'énumération chronologique complète de cette
sélection. Un pas consomme la prochaine identité avec sa charge effective ;
`choices` est exactement vide ou singleton et le rang est le nombre d'identités
restant à consommer. La trace terminale consomme donc exactement `size` charges
et normalise le curseur vers l'état `target`, l'obligation de limite elle-même.
`BatchCharge` conserve dans l'ordre chronologique, pour chaque consommation,
le code lu et le même témoin `Near`, séparément du code cible exact. Ainsi, la
règle locale de rang un décrit l'atome source–cible, tandis que la règle de lot
exécute réellement tout le regroupement fini : le rang n'est pas artificiellement
figé lorsque plusieurs sources sont présentes.

Ajouter une source construit une nouvelle sélection, injecte toutes les
anciennes identités, place la nouvelle après elles, transporte chaque ancien
pas vers une trace réelle et conserve exactement leurs codes ainsi que le code
cible. `batchExtension` étend aussi le curseur et les règles de lot ; le
transport de la charge conserve exactement la liste chronologique déjà consommée, et une
ancienne consommation produit la même liste de preuves consommées. Deux ajouts
successifs sont explicitement composés. Le contrat de futurs fournit à la fois
l'extension locale et l'extension de lot pour chaque ajout fini ; il n'efface
donc la mémoire d'aucune source ancienne.

## Relation entre local, global et readout

Le local est une demande à précision finie avec ses sources admissibles. Le
global n'est ni une liste achevée de toutes les demandes ni une fermeture du
périmètre. Il est le module effectif qui répond à toute précision et le contrat
qui prolonge tout contexte fini par les mêmes opérations et la même cible.
Une requête publique est typée soit comme source munie de son certificat
`SourceAt`, soit comme demande de limite. Toute liste finie de telles requêtes
est admise.

La construction de limite utilise la réponse diagonale
`family (modulus p)` à la précision `p`. La monotonie du module et la donnée de
Cauchy prouvent directement la cohérence entre deux précisions et la
convergence de chaque source admissible. Le code dyadique signé est le readout
de cette réponse exécutée. Il ne construit rétroactivement ni l'histoire, ni
l'occurrence, ni l'action, ni la limite relationnelle.

Le programme `executeLimitProduction` ferme l'ordre causal complet à chaque
précision : il exécute la source `modulus p`, regroupe sa charge
preuve-pertinente, puis exécute la requête de limite avec le code de sortie de
cette action. Son paquet possède les deux exécutions, l'action intermédiaire,
les témoins consommés et la preuve que son readout est l'approximation de
limite construite. Les deux requêtes ajoutent exactement douze opérations.
`FullyExecutedSequentialCompleteness` conserve un unique exécuteur maître pour
toute requête publique typée. Une requête source possède son exécution source ;
une requête limite possède le `ExecutedLimitProduction` complet, et non la
réexécution d'un payload de limite déjà formé. Une loi point par point rattache
cet exécuteur au producteur canonique. La projection `produceLimit` est donc
exactement une spécialisation de ce maître et son théorème
`produceLimitCanonical` la rattache à `executeLimitProduction`. Le paquet reste
lié au même `SequentialCompletenessResult`. Il conserve aussi, pour toute chaîne
chronologique finie effectivement exécutée, le programme de regroupement qui
consomme exactement toutes ses sources. Le raccord terminal projette sa
première production complète de ce maître universel ; il ne la recalcule pas à
côté.

Les présentations d'un réel ne sont pas quotientées.
`RelationalReal.Equivalent` porte un seuil de réponse calculable pour chaque
précision et des témoins `Near` pour toutes les réponses ultérieures. Sa
transitivité calcule un seuil commun à la précision suivante puis consomme la
loi triangulaire constructive. Les processus constants ancrent les codes
dyadiques : tout changement exact d'échelle donne une présentation
équivalente, y compris au niveau du readout exécuté.

Cette organisation donne la forme locale–globale recherchée : chaque précision
est finie et exécutée, tous les futurs finis sont couverts par un même contrat,
et leur cohérence détermine le module limite. Le pont familial
`MasterContinuation.bridge` relie l'état riche, qui conserve le journal réel,
à l'état public, qui conserve sa profondeur et le dernier code. Ses transitions
et ses événements sont deux projections du même exécuteur conservé. Il prouve,
pour toute liste finie de requêtes typées, l'égalité des états projetés, des
événements normalisés et des observations ; il transporte aussi les témoins
d'admission dans les deux sens. Deux états riches ayant la même projection ont
donc les mêmes futurs autorisés et normalisés, y compris lorsque le futur
contient une requête limite qui doit exécuter source, regroupement et limite.
Le raccord ne laisse pas cette prémisse abstraite : `groupedFutureState`
réutilise le paquet source déjà exécuté, puis exécute comme réponse suivante
le code effectivement retourné par l'action de regroupement. Le théorème
`groupedSources_project_eq` prouve que deux sources produites à des profondeurs
égales ont alors la même projection publique, et
`FullyExecutedSequentialCompleteness.groupedSourcesSameMasterFuture` en déduit
l'égalité de tous leurs futurs finis normalisés sous le maître retenu. Les
journaux riches et les identités sources ne sont pas identifiés par cette
projection.
L'apparence de continuité du readout provient de cette cohérence de réponses ;
elle ne transforme pas le regroupement en égalité extensive de toutes les
sources.

## Branche négative conservée et restriction globale

La totalité positive précédente n'est pas `P.TotalLoop`. `TotalLoop` identifie
les extrémités `Truth(G)` et `Proof(G)` et induit donc la conversion dirigée
`Truth(G) -> Proof(G)`. La vérité certifiée et la non-prouvabilité du même `G`
produisent alors `Empty`. De même, une admission de la première continuation
dans le même régime produit la tentative bilatérale, la totalisation, le noyau
de contraction et la même conversion interdite.

La fermeture globale interdite est définie par une action qui fournit une
fermeture dans le même régime à chaque profondeur finie et qui conserve le
label de chaque occurrence antérieure sous toute extension de profondeur. Elle
n'est donc pas une collection incohérente d'admissions indépendantes. Le
théorème de restriction l'évalue à la profondeur `1`, laquelle est
définitionnellement la continuation gödelienne déjà établie. C'est seulement à
ce point que
`GodelPositiveSameRegimeAdmission execution` est dérivée, puis consommée par
la chaîne précédente. Elle n'est pas supposée dans le paquet terminal.

Le raccord conserve ainsi deux conclusions simultanées sur le même témoin et
le même périmètre : la fermeture totalisante est rejetée, tandis que la
continuation locale–globale requise pour la complétude séquentielle est
effectivement construite.

## Instance de Heyting Arithmetic et limites du résultat

`RelationalPerimeter.Instances.HeytingArithmetic.RelationalCompleteness`
instancie le raccord avec l'exécution HA concrète déjà construite. Pour toute
famille de Cauchy exécutée sur cette présentation HA, il produit le paquet
terminal et son producteur universel sans ajouter d'hypothèse de vérité, de
preuve ou de fermeture.

Le résultat ne prouve pas encore une équivalence avec une construction
extensive standard des réels, la complétude par borne supérieure, la densité
ordonnée, `AC` ou `CH`. Ces questions exigent des définitions et des théorèmes
distincts. Les évoquer comme conséquences automatiques affaiblirait la cible
réellement démontrée : la complétude séquentielle effective des réels
relationnels constitués et exécutés sur le périmètre gödelien commun.
