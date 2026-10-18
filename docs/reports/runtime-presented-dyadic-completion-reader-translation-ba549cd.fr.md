# Revue de la caractérisation runtime de la complétion dyadique présentée

Responsable : Codex (OpenAI), lectures autonomes puis confrontation formelle.

Date : 18 octobre 2026.

Révision examinée : `ba549cd03552dd5d0c7f5737305c684bf7d49897`.

## Périmètre

La lecture française autonome a porté intégralement sur
`docs/runtime-presented-dyadic-completion-characterization.fr.md`. La lecture
anglaise a ensuite porté intégralement, séparément, sur
`docs/runtime-presented-dyadic-completion-characterization.en.md`. La
confrontation FR/EN et la lecture des huit modules Lean de production, des deux
modules de tests positifs et des vingt fixtures négatives ont été effectuées
après ces deux lectures.

La révision examinée ajoute les étapes 7.1 à 7.3 : production d'une limite au
niveau du carrier par la route native, contrat non circulaire de complétion
dyadique présentée, réalisation ordonnée concrète et caractérisation relative.
Elle ne choisit aucune référence classique externe et n'implémente pas l'étape
7.4.

## Lecture française

Le texte conserve l'ordre des primitives. Une `CarrierFamily` reçue est
transformée en famille native, les pas courants sont consommés par sa loi de
Cauchy, puis `nativeCompleteness` produit le paquet limite. Le carrier n'est
projeté qu'ensuite, et `CarrierCompletionResult` conserve le paquet natif
entier. Le texte ne transforme donc pas un carrier cible préfabriqué en origine
de la production.

Le noyau `PresentedDyadicStructure` reçoit seulement approximations, modules,
cohérence, injection dyadique et équivalence quantitative positive.
`PresentedDyadicCompletion.complete` reçoit une famille et produit sa valeur,
sa convergence et son unicité. Aucun morphisme terminal, inverse de readout ou
candidat limite n'est placé dans ce contrat. L'enrichissement ordonné est
correctement séparé : `PresentedDyadicOrderedFieldData` enrichit la structure,
puis `PresentedDyadicOrderedFieldCompletion` l'assemble avec une complétion.

La densité et les bornes naturelles restent des productions riches avant leur
projection. Leurs résultats conservent sondages, actions, cibles et témoins ;
les égalités de readout consomment ces ressources stockées. Les transports
relatifs ne rejouent pas le sélecteur d'une cible : ils transportent le témoin
fini reçu et son code ou ses entiers.

Le texte borne correctement les conclusions. Les allers-retours sont des
équivalences comportementales et numériques, non des égalités d'occurrences,
de fonctions ou de familles riches. La couverture des réels classiques, la
complétude par borne supérieure, l'ordre global décidable, `AC`, `CH`, le coût
physique et l'originalité restent exclus.

Verdict de lecture française : **reviewed** pour
`RUNTIME_PRESENTED_DYADIC_COMPLETION_CHARACTERIZATION` sur la révision
indiquée.

## Lecture et confrontation anglaises

La version anglaise conserve les mêmes objets, quantifications et directions.
`produced completeness`, `whole NativeCompleteness packet`, `downstream
readings`, `non-circular completion contract` et `relative characterization`
correspondent respectivement à la complétude produite, au paquet natif entier,
aux lectures aval, au contrat non circulaire et à la caractérisation relative
du texte français.

Les deux versions distinguent de la même manière la structure présentée, son
enrichissement ordonné et leur assemblage avec la complétion. Elles disent
toutes deux que la préservation des limites est dérivée, que le morphisme ne la
reçoit pas comme champ, et que les transports de densité et de bornes ne
réexécutent pas le sélecteur de la cible.

Aucune version ne transforme le readout extensif en primitive, ne promet une
fonction exécutable depuis un quotient nu, ni ne présente la caractérisation
relative comme une identification avec tous les réels classiques.

Verdict de traduction : **reviewed** pour
`RUNTIME_PRESENTED_DYADIC_COMPLETION_CHARACTERIZATION` sur la révision
indiquée.

## Confrontation aux définitions

`carrierCompletion` appelle `nativeCompleteness`, conserve son résultat dans
le champ `native`, définit `limit` par `toCarrier native.limit`, puis dérive
convergence et unicité. `carrierLimitNativeCandidate` ne reçoit qu'un candidat
pour la comparaison d'unicité et consomme séparément le pas du terme et le pas
du candidat. L'indépendance envers `P` et `baseDepth` est une équivalence issue
de cette unicité, jamais une égalité de runtimes.

`PresentedDyadicCompletion.complete` a pour seul argument une
`PresentedFamily`. `CompletionMorphism` contient `map`, `mapEquivalent`,
`mapDyadic` et `presents`; il ne contient aucun champ de préservation des
limites. `comparisonMorphism`, `preservePresentedLimit`, `mapProducedLimit` et
les allers-retours sont construits depuis la présentation, la complétude et
l'unicité.

`CarrierDensityResult` et `CarrierNaturalBoundResult` retiennent les paquets
riches. `carrierDensityReadoutExact` lit l'action et les deux `Step` de
l'origine réalisée ; l'indépendance des bornes lit les sondages conservés par
les deux paquets. Les preuves aval n'appellent ni `produceComparison` ni
`executeReal` pour reconstruire ces sorties.

`relativeOrderedCharacterization` remplit concrètement les morphismes, les
retours, les transports ordonnés et les transports de limites. Les structures
`OrderedMorphismTransports` et `RelativeOrderedCharacterization` sont des
paquets de résultats dérivés ; elles ne font pas partie du contrat minimal de
la cible. Les égalités exactes exportées portent seulement sur la forme
définitionnelle des applications aller et retour, pas sur l'identité des
carriers ou occurrences.

## Contrôles mécaniques sur la révision examinée

`lake build` réussit avec 408 jobs, sans avertissement. L'audit exhaustif porte
sur 37 882 constantes dans 405 modules, avec 759 exceptions générées par le
compilateur et aucune exception écrite. Les huit modules nouveaux contiennent
156 déclarations explicitement auditées sans axiome ; les deux tests positifs
en contiennent 78 également sans axiome.

Le contrôle compilé `check-real-carrier-completion-codegen.py` valide quatre
routes et rejette vingt-huit mutations. Le harnais des échecs attendus valide
209 fixtures sur ses façades Bash et PowerShell, avec diagnostic et site
exacts. La stratification, les frontières d'import et `git diff --check`
réussissent. Les sept autotests documentaires réussissent.

La gate documentaire statique globale s'arrête encore sur
`STALE_SOURCE: GODEL_RELATIONAL_SEQUENTIAL_COMPLETENESS`. Cette empreinte
antérieure n'a pas été actualisée mécaniquement et ce blocage n'est pas présenté
comme une réussite du présent lot.

La présente revue n'est pas indépendante. Le champ `independent` doit rester
`not_recorded` jusqu'à réception et lecture d'un rapport extérieur visant
exactement la révision indiquée.
