# Référence cauchyenne régulière conventionnelle et réalisation runtime

## Statut et portée

Ce passage est le texte canonique de l'affirmation
`RUNTIME_CONVENTIONAL_REGULAR_CAUCHY_REFERENCE`. Il fixe dans le dépôt une
référence autonome des réels de Cauchy dyadiques réguliers, puis établit sa
correspondance relationnelle avec le carrier numérique et le runtime déjà
constitués.

La référence comprend toute fonction reçue des précisions naturelles vers les
codes dyadiques signés, accompagnée de sa régularité positive. Elle ne se
limite donc pas aux programmes fermés du dépôt. Elle n'est toutefois pas
identifiée définitionnellement à `Mathlib.Real`, aux coupures de Dedekind ou à
une autre construction externe non formalisée ici.

L'ordre des primitives reste constitutif. Les relations, exécutions, actions,
mémoires et limites runtime sont produits avant leurs readouts. Les noms et
les classes extensives définis dans ce passage sont des comparaisons aval ;
ils ne reconstruisent aucune occurrence, histoire, archive, banque, journal
ou ressource oubliée.

## Conclusion formelle sur les noms réguliers

Un `RegularDyadicName` contient une approximation
`Nat -> SignedDyadicCode` et une loi positive de régularité. À toute précision
demandée, deux réponses suffisamment fines du même nom sont reliées par
`Near`. `NameEquivalent` relie deux noms lorsqu'un seuil de réponse partagé
permet d'obtenir cette proximité à toute précision demandée.

La réflexivité, la symétrie et la transitivité de `NameEquivalent` sont
construites positivement. Les constantes dyadiques conservent exactement la
valeur du code reçu. L'opposé lit la précision demandée, l'addition lit un cran
supplémentaire et la multiplication sonde chacun des facteurs à précision zéro
avant d'affiner l'autre selon l'amplitude obtenue. Ces opérations et leurs lois
ne passent par aucun carrier ou runtime.

`NameOrder` et `NameApartness` portent des marges orientées positives. Le
transport de l'ordre aligne explicitement sept bornes dirigées : trois liens
fins de chaque côté et le lien central. L'inverse reçoit un témoin positif
d'apartness à zéro. La densité dyadique et les bornes naturelles produisent
leurs codes et entiers depuis les réponses finies effectivement lues.

Le paquet `regularOrderedCompletion` ferme sur les noms réguliers les lois de
corps ordonné constructif, la densité et les bornes. Il réalise concrètement le
contrat `PresentedDyadicOrderedFieldCompletion` sans hypothèse terminale vers
le runtime ou vers une classe extensive.

## Complétion produite

Une `RegularPresentedFamily` reçoit ses noms, un module extérieur monotone et
sa loi de Cauchy. Sa limite n'est pas fournie comme candidat :
`regularLimitResult family` produit `diagonalName family`, qui lit le terme
sélectionné par le module à la précision demandée. Le même nom produit fournit
ensuite la convergence et l'unicité positive.

`regularPresentedCompletion.complete` réutilise exactement ce producteur.
`conventionalCompletionObject` est donc une réalisation concrète du contrat de
complétion dyadique présentée dont le carrier est exactement
`RegularDyadicName`, l'équivalence exactement `NameEquivalent` et le module
propre l'identité.

Une `ExternalPresentedFamily` ajoute à chaque terme extensif un nom membre
explicite. `referenceFamily` copie ces noms, le module et la même loi de Cauchy.
`externalComplete` appelle une seule fois la complétion régulière et utilise le
même nom produit pour la classe résultat, sa convergence et son unicité. Il ne
complète pas une fonction nue `Nat -> Value` privée de noms membres et de
module.

## Classes extensives sans représentant choisi

Une `ExtensiveCauchyReal.Value` est une relation `Contains` sur les noms,
saturée par `NameEquivalent` et cohérente : deux noms membres sont positivement
équivalents. Son inhabitance est cachée sous `Nonempty`. Aucun champ ne choisit
un représentant en `Type`.

`classOf name` construit la classe exacte d'un nom. `ExternalEquivalent`
transporte positivement les appartenances dans les deux sens ; il n'identifie
pas les prédicats `Contains` par égalité. `classOf` préserve et réfléchit
`NameEquivalent` et toute valeur est propositionnellement équivalente à une
classe ainsi construite.

`ConventionalRegularCauchyReference` a exactement
`Carrier := RegularDyadicName` et `Equivalent := NameEquivalent`.
`ReferenceRealizes name value` est exactement `value.Contains name`.
`referenceCoverage` couvre constructivement chaque nom, tandis que
`valueReferenceCoverage` couvre chaque valeur seulement sous `Nonempty`. Cette
seconde direction ne peut pas être éliminée vers une fonction choisissant un
nom.

`ClassDescent` donne la propriété universelle relationnelle de cette
spécification quotient : toute application de noms respectant
`NameEquivalent` descend en un graphe total, stable et fonctionnel à
l'équivalence cible près. Son exactitude sur `classOf` et son unicité sont
prouvées sans fonction de représentants.

Les opérations extensives sont construites directement à partir des noms
membres et de leurs appartenances. Les lois positives complètes restent sur
les noms. Sur une `Value` nue, équivalence, ordre, apartness, inverse,
densité, bornes et lois algébriques sont des readouts propositionnels
explicites. Aucun `Nonempty` n'est éliminé pour fabriquer un témoin positif en
`Type`.

## Propriété universelle de complétion

La propriété universelle du quotient précédent est distincte de celle de la
complétion. Un `RelationalCompletionMorphism Target` ne contient qu'un
`CompletionMorphism conventionalCompletionObject Target`. Son graphe sur les
classes est définitionnellement la descente relationnelle de l'application de
ce pullback.

Pour toute autre `Target : PresentedDyadicCompletionObject`, la complétude de
la cible construit `relationalCompletionComparison Target`. L'unicité de deux
de ces morphismes est dérivée de la cohérence des noms membres, de la
préservation de `NameEquivalent` et de l'unicité déjà prouvée des morphismes de
complétion. Les constantes dyadiques et les limites produites sont transportées
par ce même graphe ; aucun graphe indépendant n'est supposé.

`quotientRecognition` et `completionRecognition` assemblent respectivement la
spécification quotient et la complétion relationnelle ordonnée et
archimédienne. La reconnaissance de la complétion consomme
`regularPresentedCompletion`, `regularOrderedCompletion`, le readout setoïdal
et les morphismes construits. Elle ne reçoit pas la conclusion comme champ
d'une interface externe.

## Correspondance carrier–classes

Pour toute présentation périmétrale `P` et toute profondeur `baseDepth`,
`regularCharacterization P baseDepth` instancie la caractérisation relative de
la gate précédente avec `regularOrderedCompletion`. Elle construit les
applications

```text
carrierToReferenceName : EffectiveCauchyReal.Carrier -> RegularDyadicName
referenceNameToCarrier : RegularDyadicName -> EffectiveCauchyReal.Carrier
```

et leurs retours à l'équivalence positive près. Ces applications, leurs lois
sur les constantes, opérations, ordre, apartness, inverse, densité, bornes et
limites sont des résultats dérivés de la complétion présentée et de son
unicité.

`Realizes carrier value` est exactement
`ClassDescent referenceNameToCarrier value carrier`. Toute preuve de
réalisation porte donc son nom membre, son appartenance à la classe et son
accord avec le carrier. `carrierCoverage` associe à chaque carrier la classe de
son nom obtenu par l'application aller et consomme le retour prouvé.
`relationalCoverage` couvre chaque valeur dans l'autre sens uniquement sous
`Nonempty`.

La correction montre que deux carriers équivalents réalisent des valeurs
`ExternalEquivalent`. La fidélité montre que deux réalisations de valeurs
externes équivalentes ont des carriers équivalents. Les transports et leurs
réflexions réutilisent la même caractérisation relative : aucune seconde
opération ou relation n'est reconstruite.

Pour les familles et les limites, `carrierExternalFamily` conserve les termes,
le module et les noms produits par `carrierCoverage`. Deux paquets de
complétion déjà produits sont comparés par la convergence du candidat externe
et l'unicité carrier. La route inverse utilise le transport diagonal explicite
de la caractérisation relative ; ces deux familles et leurs modules ne sont
pas identifiés silencieusement.

## Réalisation runtime

`RuntimeRealizes runtime value` est exactement
`Realizes (toCarrier runtime) value`. `runtimeCoverage` donne donc à tout
runtime une valeur aval qu'il réalise. `valueRuntimeCoverage` part de la
couverture relationnelle d'une valeur, construit `ofCarrier` uniquement à
l'intérieur de `Nonempty` et transporte l'accord par `carrier_roundtrip`.
Aucune fonction `Value -> Real P baseDepth` n'est obtenue.

Pour chaque nom régulier explicitement reçu,
`runtimeOfReferenceName P baseDepth name` applique en revanche
`referenceNameToCarrier` puis `ofCarrier`. Cette construction est exécutable
parce que le nom, et non une classe nue, est une entrée déclarée.
`runtimeOfReferenceNameRealizes` prouve que ce runtime réalise `classOf name`.
Cette application retour est une route de comparaison aval ; elle ne devient
pas l'origine des producteurs runtime natifs et ne récupère aucune histoire
effacée.

Les transports runtime des opérations, de l'ordre, de l'apartness, de
l'inverse, de la densité et des bornes passent par les théorèmes de readout
déjà établis puis par la correspondance carrier. Les transports de densité et
de bornes consomment les paquets riches reçus et conservent exactement leurs
codes ou entiers. Le transport d'une limite consomme `carrierProduced.native.limit`
et l'égalité `limitExact` du même paquet ; il ne fabrique aucun second runtime
limite.

## Verdict exact et non-conclusions

`recognizesConventionalCauchyReference P baseDepth` rassemble les quatre
paquets construits : `QuotientRecognition`, `CompletionRecognition`,
`CarrierValueCorrespondence` et `RuntimeValueCorrespondence`. Il établit la
correspondance avec tous les éléments de la référence cauchyenne régulière
fixée dans ce passage, y compris tout nom régulier reçu, et non seulement les
termes effectifs fermés antérieurement.

Le sens constructif porte sur les noms explicitement reçus et sur les carriers.
Le sens partant d'une classe extensive nue reste relationnel et
propositionnellement tronqué. Les allers-retours n'identifient ni fonctions,
occurrences, familles riches, programmes, mémoires ou preuves.

Ce résultat ne prouve pas une identité avec `Mathlib.Real`, une construction de
Dedekind ou tout autre modèle non formalisé dans le dépôt. Il ne prouve ni
complétude par borne supérieure, ni ordre globalement décidable, ni choix de
représentants, ni énumération de tous les réels par un programme fini. Aucune
conclusion sur `AC`, `CH`, le coût physique ou l'originalité ne découle de cette
affirmation.
