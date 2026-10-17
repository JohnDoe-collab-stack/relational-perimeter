# Correspondance runtime–réel de Cauchy effectif

## Statut et portée

Ce passage est le texte canonique de l'affirmation
`RUNTIME_EFFECTIVE_CAUCHY_REAL_CORRESPONDENCE`. Il décrit une correspondance
constructive entre comportements runtime, présentations dyadiques effectives
et carriers de Cauchy effectifs. Il ne constitue ni un audit indépendant, ni
une identification des histoires riches, ni une construction de tous les réels
classiques.

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

La correspondance couvre exactement les présentations dyadiques et les réels
de Cauchy effectivement présentés par les données reçues. Elle ne couvre pas
tous les réels classiques. Elle ne prouve pas le transport de l'addition, de
la multiplication, de l'ordre ou de l'apartness, la densité, la propriété
archimédienne, la complétude d'ordre, `AC` ou `CH`. Ces propriétés exigent des
constructions et des affirmations séparées.
