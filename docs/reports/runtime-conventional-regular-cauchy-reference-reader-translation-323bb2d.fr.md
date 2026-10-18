# Revue de la référence cauchyenne régulière conventionnelle

Révision examinée : `323bb2d72724804dc38a93316127a1efcba3042a`.

## Portée et méthode

Cette revue porte sur l'affirmation
`RUNTIME_CONVENTIONAL_REGULAR_CAUCHY_REFERENCE`. Le passage français a été lu
autonomement, puis le passage anglais a été lu autonomement. Les conclusions
textuelles ont ensuite été confrontées aux types complets, aux corps Lean, aux
tests positifs et aux fixtures négatives de la même révision.

La revue n'est ni un audit indépendant ni une affirmation d'identité avec
`Mathlib.Real`, les coupures de Dedekind ou un autre modèle extérieur non
formalisé dans le dépôt.

## Lecture française autonome

Le texte français fixe sans ambiguïté la cible : la référence conventionnelle
est le type de tous les `RegularDyadicName` reçus, muni de
`NameEquivalent`, et non une énumération de programmes fermés. Les classes
extensives sont des relations saturées et cohérentes sur ces noms ; elles ne
stockent aucun représentant choisi. La complétion produit sa diagonale au lieu
de recevoir un candidat. Les correspondances carrier et runtime sont des
routes aval, et la direction partant d'une classe nue reste sous `Nonempty`.

Le passage distingue explicitement la propriété universelle de descente des
classes de la propriété universelle de complétion. Il n'annonce ni identité
d'occurrences, ni récupération d'histoires, ni complétude par borne
supérieure, ni conséquence sur `AC` ou `CH`.

## Lecture anglaise autonome et traduction

Le texte anglais conserve exactement cette cible. Les formulations « every
received function », « no field selects a representative in `Type` »,
« invokes regular completion once » et « downstream comparison route »
restituent les quantifications et la direction des primitives du texte
français. `Nonempty` reste traduit comme une troncature propositionnelle et
non comme un choix caché. Les non-conclusions sont symétriques.

La traduction française/anglaise est validée.

## Confrontation formation–exécution–preuve–transport

| Question | Constat sur la révision examinée |
| --- | --- |
| Formation | `RegularDyadicName` reçoit `Nat -> SignedDyadicCode` et sa régularité. `RegularPresentedFamily` reçoit noms, module monotone et loi de Cauchy. `Value` contient `Contains : RegularDyadicName -> Type`, une inhabitance sous `Nonempty`, saturation et cohérence, sans représentant. L'inverse reçoit un témoin positif d'apartness. |
| Construction exécutée | `diagonalName` lit le terme sélectionné par le module. `regularLimitResult` construit cette diagonale, sa convergence et son unicité. `externalComplete` lie une seule production régulière et réutilise sa valeur pour la classe, la convergence et l'unicité. Les opérations sur noms lisent effectivement les précisions et sondes annoncées. |
| Preuve consommée | `NameEquivalent` est construit comme équivalence positive. L'ordre transporte trois liens fins de chaque côté et le lien central. `classDescent` consomme un nom membre et son accord ; son unicité consomme cohérence, stabilité et extension. Les morphismes de complétion sont produits par la complétude cible et leur unicité, non reçus comme conclusion. |
| Projection et oubli | `classOf` et `ExternalEquivalent` n'identifient pas les prédicats par égalité. `valueReferenceCoverage`, `relationalCoverage` et `valueRuntimeCoverage` restent `Nonempty`. La route exécutable `runtimeOfReferenceName` exige un nom explicitement reçu. Les readouts sur `Value` restent propositionnels et ne recréent aucun témoin positif en `Type`. |

## Obligations critiques contrôlées

- `ConventionalRegularCauchyReference.Carrier` est exactement
  `RegularDyadicName` et son équivalence exactement `NameEquivalent`.
- `regularPresentedCompletion.complete` réutilise `regularLimitResult` ; le
  candidat limite n'est pas un argument.
- `externalComplete` appelle une seule production régulière et ne reçoit pas
  une suite nue de classes.
- `ClassDescent.total` élimine l'inhabitation tronquée seulement pour produire
  un résultat lui-même sous `Nonempty`; aucune fonction de choix
  `Value -> RegularDyadicName` n'en résulte.
- `carrierCoverage` est constructive depuis un carrier ; la direction depuis
  une `Value` nue est `Nonempty`.
- `runtimeCoverage` part d'un runtime constitué ; la direction depuis une
  `Value` nue reste `Nonempty`, tandis que la route depuis un nom reçu est une
  fonction séparée.
- Le transport de limite runtime consomme la limite native et l'exactitude du
  même paquet produit ; il ne fabrique pas un second runtime limite.
- Les tests comportent des noms à réponses distinctes mais équivalents, des
  familles reçues non constantes, des witnesses d'inverse distincts et des
  réalisations portant des noms différents.
- Les fixtures négatives interdisent notamment le représentant stocké, le
  sélecteur de classe, le faux carrier fini, la cible diagonale de rechange,
  le graphe indépendant et la reconstruction d'un runtime depuis une classe
  nue.

## Verdict

Les revues `reader` et `translation` sont validées sur la révision exacte
examinée. Le code atteint la cible interne annoncée : correspondance avec la
référence autonome de tous les noms cauchyens dyadiques réguliers reçus, avec
descente relationnelle des classes et réalisation runtime. Il ne prouve pas
une identité avec un modèle externe non formalisé ni une complétude d'ordre.
Le statut `independent` reste une obligation séparée.
