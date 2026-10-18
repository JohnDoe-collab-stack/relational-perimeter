# Caractérisation runtime de la complétion dyadique présentée

## Statut et portée

Ce passage est le texte canonique de l'affirmation
`RUNTIME_PRESENTED_DYADIC_COMPLETION_CHARACTERIZATION`. Il décrit la
complétude produite du carrier relationnel et sa caractérisation relative
parmi les complétions dyadiques constructives explicitement présentées.

La caractérisation porte sur des données exécutables : approximations
dyadiques signées, modules explicites, lois positives de cohérence et familles
de Cauchy munies de leurs témoins. Elle ne part pas d'un type extensif de réels
et ne construit pas tous les réels classiques. Les comportements, exécutions
et productions riches restent constitutifs ; le carrier numérique et les
présentations comparées sont des lectures aval.

## Conclusion formelle de complétion dyadique présentée

Pour toute présentation périmétrale `P`, toute profondeur `baseDepth` et toute
`CarrierFamily` explicitement reçue, `carrierCompletion P baseDepth family`
construit un `CarrierCompletionResult`. Le résultat conserve le paquet
`NativeCompleteness` entier de la famille native correspondante, puis projette
sa limite produite en `EffectiveCauchyReal.Carrier`. Il fournit une loi de
convergence pour la famille carrier initiale et établit l'unicité de cette
limite à `EffectiveCauchyReal.Equivalent` près.

La production ne reçoit aucun candidat limite. `carrierNativeFamily` forme la
famille native depuis les termes, le module extérieur et les modules propres
des termes. Sa loi de Cauchy consomme les `Step` courants possédés par les
exécutions et les raccorde aux approximations normalisées reçues.
`nativeCompleteness` exécute ensuite la production et le regroupement natifs.
La projection `toCarrier native.limit` intervient seulement après cette
production et le paquet natif reste disponible dans le résultat.

`carrierCompletion_perimeterIndependent` compare deux productions obtenues à
partir de la même famille carrier sur deux présentations ou profondeurs. Sa
conclusion est une équivalence numérique positive dérivée de l'unicité ; elle
n'identifie ni les runtimes, ni leurs archives, journaux ou occurrences.

## Contrat non circulaire de complétion

`PresentedDyadicData` reçoit un type de carriers, leurs approximations et
modules, les lois positives de monotonie et de cohérence, ainsi que l'injection
des codes dyadiques et son exactitude. `PresentedDyadicStructure` ajoute une
équivalence positive reliée dans les deux sens à l'équivalence quantitative
des approximations.

Une `PresentedFamily` contient ses termes, son module extérieur monotone et sa
loi de Cauchy. `Converges` expose un seuil et les comparaisons quantitatives
requises. `PresentedDyadicCompletion.complete` reçoit seulement la famille et
doit produire un `LimitResult` comprenant la valeur, sa convergence et son
unicité. Aucun candidat limite, aucune application terminale et aucun inverse
de readout ne figurent dans ce contrat.

La réalisation `carrierCompletionStructure P baseDepth` ferme concrètement ce
contrat pour `carrierPresentedCore` en appelant la production native précédente.
Les familles canoniques d'addition, d'opposé et de multiplication spécifient
uniquement le comportement numérique attendu ; elles ne définissent pas un
producteur runtime et ne choisissent pas une famille reçue arbitraire.

## Réalisation ordonnée et témoins finis

`PresentedDyadicOrderedFieldData` enrichit une complétion présentée par zéro,
unité, addition, opposé, multiplication, inverse sous apartness, ordre
constructif, lois algébriques, lois d'ordre, densité dyadique et bornes
naturelles. Les convergences des opérations vers leurs familles canoniques font
partie du contrat. `PresentedDyadicOrderedFieldCompletion` réunit ce paquet et
la complétion, sans supposer de morphisme de comparaison.

`carrierOrderedCompletion P baseDepth` réalise concrètement ce contrat. Les
opérations du carrier sont des readouts numériques déjà raccordés aux
opérations runtime constituées. Leurs lois sont transportées depuis les
producteurs relationnels et leurs théorèmes de readout ; elles ne sont pas
réimportées pour fabriquer ces producteurs.

La densité et les bornes naturelles sont d'abord construites comme
`CarrierDensityResult` et `CarrierNaturalBoundResult`. Ces paquets retiennent
les comportements réalisés, les sondages, actions, cibles et témoins d'ordre
produits. Le contrat ordonné n'en projette les codes et bornes qu'après cette
production. Les théorèmes d'indépendance des readouts consomment les `Step` et
actions retenus ; ils ne reconstruisent pas une comparaison indépendante.

Les transports quantitatifs paient explicitement leurs pertes de précision.
La congruence multiplicative conserve les amplitudes croisées requises et le
transport de l'ordre aligne les sept certificats sur une précision commune.
Aucune cofinalité de module, décision globale d'ordre ou arithmétique classique
n'est supposée.

## Caractérisation relative

Un `CompletionMorphism Source Target` contient une application, la
préservation de l'équivalence, l'accord sur les constantes dyadiques et la
présentation numérique de chaque image. Il ne contient ni inverse, ni loi
d'aller-retour, ni préservation des limites comme hypothèse.

`comparisonMorphism Source Target` est produit par la complétude de la cible à
partir de la présentation numérique de la source. Son unicité point par point
est dérivée de l'unicité des limites. `preservePresentedLimit` et
`mapProducedLimit` dérivent la préservation des limites au moyen d'une famille
diagonale renforcée ; cette préservation n'est pas un champ reçu du morphisme.

Pour toute `Target : PresentedDyadicOrderedFieldCompletion`,
`relativeOrderedCharacterization P baseDepth Target` construit les morphismes
aller et retour entre la complétion carrier et `Target`. Il établit leurs
retours à l'équivalence comportementale près, la préservation et la réflexion
de l'équivalence, de l'ordre et de l'apartness, la préservation de zéro, un,
addition, opposé, multiplication et inverse, ainsi que le transport de la
densité, des bornes et des limites produites dans les deux directions.

Les transports de densité et de bornes conservent le code ou les entiers du
témoin reçu ; ils n'exécutent pas le sélecteur propre de la cible. Les
allers-retours ne sont pas des égalités de fonctions, de carriers,
d'occurrences ou de familles riches. Ils ne récupèrent pas les modules,
témoins de Cauchy, banques, archives ou journaux oubliés par le readout.

## Non-conclusions

Cette caractérisation couvre les familles de Cauchy explicitement présentées
par `CarrierFamily` et toute cible constructive satisfaisant le contrat
`PresentedDyadicOrderedFieldCompletion`. Elle établit une caractérisation
relative de complétion dyadique présentée, pas une identification avec une
construction classique externe particulière.

Elle ne prouve ni la couverture de tous les réels classiques, ni la complétude
par borne supérieure, ni un ordre globalement décidable. Aucune fonction
exécutable depuis un quotient extensif nu n'est construite. Une comparaison
avec les réels usuels exige encore une référence externe exacte et une gate
séparée prouvant totalité, correction, fidélité et transports structurels dans
la portée choisie. Aucune conclusion sur `AC`, `CH`, le coût physique ou
l'originalité ne découle de ce résultat.
