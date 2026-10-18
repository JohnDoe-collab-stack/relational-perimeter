# Correspondance runtime–réel de Cauchy effectif

## Statut et portée

Ce passage est le texte canonique de l'affirmation
`RUNTIME_EFFECTIVE_CAUCHY_REAL_CORRESPONDENCE`. Il décrit une correspondance
constructive et structurelle entre comportements runtime, présentations
dyadiques effectives et carriers de Cauchy effectifs. Cette correspondance
comprend les opérations et relations effectivement construites dans le
porteur relationnel, ainsi que ses familles de Cauchy et leurs limites. Elle ne
constitue ni un audit indépendant, ni une identification des histoires riches,
ni une construction de tous les réels classiques.

## Conclusion formelle de correspondance runtime–réel effectif

`EffectiveDyadicPresentation` reçoit une fonction calculable
`approximation : Nat -> SignedDyadicCode` et une loi positive de cohérence pour
toute paire de précisions raffinant une précision commune.
`presentationToRuntime P baseDepth presentation` construit une
`ExecutedCauchyFamily P baseDepth` dont le producteur calcule l'approximation à
la précision demandée et dont le module est l'identité, puis son `RuntimeReal`
autoritatif.

Dans l'autre sens, `runtimeToPresentation real` obtient chaque approximation
en exécutant le pas limite canonique depuis l'état initial du runtime et en
lisant la réponse que ce pas possède. `RuntimeReal.ReadoutOrigin` conserve, à
chaque précision, le pas produit, son égalité au pas canonique et l'égalité
exacte entre son readout mémorisé et le readout exposé.

L'aller-retour depuis une présentation est exact à chaque précision par
`presentation_roundtrip_readout_exact`. L'aller-retour depuis un runtime est
une `RuntimeReadoutEquivalent`. `runtimeReadoutCorrespondence` rend cette
équivalence numérique inter-dérivable avec l'équivalence positive des
présentations produites par readout. Aucune de ces constructions ne conclut à
l'égalité des états, journaux, ressources, programmes ou occurrences riches.

Au-dessus de ce raccord numérique, `effectiveCorrespondence P baseDepth`
construit la correspondance structurelle pour le porteur runtime fermé :
applications et allers-retours, constantes, addition, opposé, multiplication,
inverse sous apartness à zéro, ordre constructif, densité et bornes finies,
familles de Cauchy source et natives, limites, complétude effective et unicité
numérique. Ses six blocs sont remplis par les producteurs et théorèmes du
dépôt ; leur conclusion n'est pas supposée par le constructeur. Les transports
vers présentations et carriers restent des readouts aval et n'identifient pas
les données riches oubliées.

## Futurs limites effectivement retenus

Une `LimitQuery` sépare la précision de comparaison des précisions de réponse
choisies au-delà du seuil. `RuntimeReadoutEquivalent.toLimitFuture` exécute les
listes de requêtes limites correspondantes par `run` et construit une
`PairedLimitTrace` sur les deux traces réellement retenues. Chaque pas conserve
les deux `ExecutedStep`, l'égalité des profondeurs initiales et la relation
`Near` entre leurs readouts ; la profondeur terminale est dérivée de ces mêmes
pas. `LimitFutureEquivalent.toReadouts` récupère la loi numérique depuis une
trace singleton. Les readouts et les futurs limites finis sont ainsi
inter-dérivables, sans identifier les pas riches.

Le runtime commun fournit un raccord complémentaire entre environnements.
`CommonRealRuntime.NumericalFutureEquivalent` apparie les transitions limites
effectivement exécutées par `performReal` à partir de mémoires arbitraires dans
deux environnements. `numericalFutureCorrespondence` l'identifie exactement à
`RuntimeReadoutEquivalent` au seul niveau numérique. L'environnement —
producteur et module — reste une donnée du runtime ; cette relation ne devient
jamais une `FutureEquivalent` exacte entre programmes différents.

## Carrier effectif externe

`EffectiveCauchyReal.Carrier` contient une suite exécutable de codes dyadiques
signés, un module explicite, la monotonie positive de ce module et une loi de
Cauchy. `toPresentation` diagonalise la suite par son module ;
`ofPresentation` construit le carrier canonique à module identité. Les deux
sens et leurs allers-retours sont reliés par `EffectiveCauchyReal.Equivalent`,
sans quotient et sans choix classique.

`fromRuntime` lit un carrier depuis la présentation aval du runtime.
`toRuntime` construit un runtime depuis le carrier reçu.
`runtimeCarrierCorrespondence` rend l'équivalence des readouts runtime
inter-dérivable avec l'équivalence des carriers ainsi lus, et
`carrier_runtime_roundtrip_equivalent` établit l'aller-retour d'un carrier reçu.
La réciproque reconstruisant une histoire runtime depuis les seules valeurs
numériques n'est ni définie ni revendiquée.

## Correspondance structurelle effective

Le porteur `RelationalRealAddition.Real P baseDepth` est fermé syntaxiquement
par les cinq constructeurs `leaf`, `add`, `neg`, `mul` et `certified`.
`certified` reçoit toutefois un `CertifiedService` extérieur muni de ses lois
de cohérence et d'uniformité : le type inductif est fermé, mais son contenu
reste ouvert relativement à cette interface reçue. Ses objets restent des
comportements exécutables : leurs environnements riches conservent les
archives, productions, actions et occurrences, puis leurs environnements live
projettent exactement la mémoire requise par le contrat de futurs fixé. Les
fonctions `toPresentation` et `toCarrier` sont des readouts aval ; elles ne
forment aucun de ces objets.

`effectiveCorrespondence P baseDepth` construit sans hypothèse terminale un
paquet `EffectiveCorrespondence` comprenant six blocs. `ApplicationMaps`
fournit les applications vers et depuis les présentations et carriers, leurs
allers-retours à `Equivalent` et `NumericalFutureEquivalent` près, ainsi que la
préservation et la réflexion des équivalences numériques. Ces allers-retours
ne sont jamais des égalités d'occurrences ou de familles riches.

`OperationTransports` raccorde les constantes dyadiques, zéro, unité,
l'addition, l'opposé et la multiplication aux opérations correspondantes sur
les présentations et carriers. L'inverse reste partiel : sa formation exige un
témoin positif d'`Apartness` à zéro, conservé séparément de l'action qui
produit l'inverse. Chaque opération relationnelle est exécutée d'abord depuis
les archives courantes de ses arguments ; le théorème de transport porte
ensuite son readout. Aucune opération numérique n'est réimportée pour fabriquer
rétroactivement le runtime.

`RelationTransports` préserve l'ordre strict et l'apartness et les réfléchit
sur les images des applications en exécutant des comparaisons fraîches depuis
les archives reçues. L'ordre n'est pas rendu décidable globalement. Les lois
de `ConstructiveOrderedFieldLaws` et de
`ConstructiveOrderedFieldFutureLaws` comprennent le groupe additif, les lois
multiplicatives, l'unité positive, les lois constructives de l'ordre, la
compatibilité avec addition et multiplication positive, et les deux lois de
l'inverse sous son domaine explicite. Elles concluent à l'équivalence de
readouts et de futurs, jamais à l'identité des arbres d'occurrences.

`OrderAndFiniteWitnesses` conserve aussi les producteurs de densité dyadique et
de bornes naturelles. Ces producteurs reçoivent les témoins d'ordre et les
archives courantes, exécutent leurs sondages et actions, puis projettent les
ordres des mêmes cibles produites vers les présentations et carriers. Il s'agit
de témoins finis construits, non d'une invocation de complétude d'ordre.

## Familles exécutées, regroupement et limites natives

`FamilyCorrespondence` distingue les familles-source
`ExecutedCauchyFamily`, les `EffectiveFamily` numériques, les familles de
carriers et les `NativeCauchyFamily` dont les termes sont eux-mêmes des
comportements du porteur fermé. Les transports source conservent le producteur
et le module déclarés et établissent les équivalences terme par terme ; ils ne
récupèrent pas, depuis leurs codes, les histoires ou témoins Cauchy oubliés.

Pour une famille native, le noyau live de chaque terme et son raccord au pas
riche sont fournis séparément. À chaque demande, la production de limite part
de la banque d'archives courante, exécute le terme diagonal choisi par le
module, fait consommer ce même `Step` par le regroupement, installe la cible
produite et poursuit le journal. La banque suivante ne remplace que l'entrée
effectivement visitée. La projection live conserve le code installé ; elle
n'exécute pas à nouveau la production riche. À chaque requête numérique,
`nativeLiveStep` ignore la mémoire live courante et exécute le
`LiveEnvironment` du kernel sélectionné depuis son champ `initial`. La fabrique
`ofTerms` forme ce champ par projection de l'archive initiale riche ; pour une
famille générique reçue, c'est la loi reçue `kernelExact`, et non l'origine du
champ à elle seule, qui raccorde cette réponse au code de tout `Step` riche
courant du même terme et de la même précision. Ce contrat d'uniformité, et non
une identification des archives, autorise l'oubli de la banque et de l'histoire.

Les constructeurs des archives riches sont `private` : par l'interface Lean
ordinaire, les fabriques publiques peuvent recevoir les contextes enfants ou
la banque courante, mais ne permettent pas de prescrire un dernier code, une
cible installée ou un historique retenu. Cette confidentialité est une
frontière d'élaboration, pas un théorème d'inforgeabilité contre un
métaprogramme visant volontairement le nom interne compilé. Les fixtures
négatives contrôlent l'usage ordinaire de l'interface publique dans cette
portée exacte.

`nativeCompleteness` construit le candidat autoritatif, sa convergence, le
readout effectif, la correspondance avec la limite produite de la famille
réalisée et l'unicité native. La transition de limite installe sa cible et
`nativeNext_read` en donne la relecture exacte ; ce champ installé est une
mémoire d'observation publique, non une entrée du calcul riche suivant, lequel
continue la banque et le journal.

`nativeUnique` compare deux candidats reçus de la même famille par une
médiation native directe. À chaque requête, elle exécute un seul pas du terme
depuis la banque courante de la trace — initialisée par `initialBank` dans
l'équivalence exportée —, passe cette même donnée aux deux lois de convergence,
puis continue son successeur dans la banque et les deux archives candidates.
`toEffectiveFamily`, `realizedFamily` et `asExecutedCandidate` restent confinés
à la correspondance numérique aval ; ils ne constituent plus cette unicité.
La conclusion est `Equivalent` avec `NumericalFutureEquivalent`; elle ne peut
pas identifier les constructeurs, archives ou occurrences des candidats.

À service, archive et précision fixés, `Step` décrit un paquet déterministe :
une réévaluation pure aux mêmes indices lui est propositionnellement égale.
« Partager le même `Step` » signifie donc que la route canonique lie une seule
donnée produite et la transmet deux fois dans la même trace ; cela ne fournit
pas un jeton génératif capable de distinguer deux évaluations identiques. La
position dans la trace et les archives continuées portent l'identité
historique. Les types rejettent un code nu, une archive étrangère ou un indice
différent, mais pas une réévaluation aux mêmes indices.

`LimitCorrespondence` conserve séparément la préservation d'une limite vers
son readout, sa réflexion et sa réalisation, la route issue d'une famille
source retournée, les limites de carriers, l'unicité numérique et la trace
riche dont la projection donne les futurs numériques. La preuve consomme les
pas terme/candidat reçus dans les producteurs et traces canoniques ; une cible
préfabriquée ou un code nu ne peut pas les remplacer. Cette garantie porte sur
la provenance typée et la continuation, avec la limite de réévaluation pure
explicitée ci-dessus.

## Raccord au périmètre de Gödel

Pour toute `ExecutedGodelProduction`, `realizePresentation` et
`realizeCarrier` placent les constructions sur exactement
`godelPerimetralPresentation execution` à la base historique `H1`. Le paquet
contient simultanément le raccord gödelien, le runtime positif, la
correspondance numérique, les futurs limites retenus et la provenance des
readouts. Les égalités `godelInitialIsRuntimeInitial`,
`godelProducedRealIsRuntimeProduced` et `godelFirstStepIsRuntimeStep` empêchent
de juxtaposer une seconde exécution indépendante au paquet Gödel.

L'instance d'arithmétique de Heyting ferme concrètement les paramètres
gödeliens. La présentation ou le carrier numérique demeure une entrée reçue :
la vérité et la non-prouvabilité gödeliennes rejettent la fermeture totale mais
ne calculent aucune approximation.

## Non-conclusions

La correspondance couvre le porteur relationnel fermé construit dans le dépôt,
les présentations dyadiques effectives et les carriers ou familles de Cauchy
effectivement présentés par les données reçues. Elle établit, dans cette portée,
les transports structurels, la densité dyadique exécutée, les bornes naturelles
et la complétude de Cauchy effective décrits ci-dessus.

Elle ne couvre pas tous les réels classiques et ne prouve pas la complétude par
borne supérieure. Elle n'identifie pas les familles, programmes, archives,
journaux, témoins Cauchy ou occurrences qui possèdent les mêmes readouts. La
loi d'un `NativeCandidate` demeure une entrée générique reçue, et le constructeur
`certified` admet tout service extérieur qui satisfait son contrat explicite. La
minimalité des mémoires est toujours relative à un environnement et à un
contrat de futurs fixés ; elle n'est ni une borne de coût physique ni une
certification universelle des captures de callbacks. Enfin, aucune conclusion
sur `AC`, `CH` ou l'originalité n'est dérivée de cette correspondance.
