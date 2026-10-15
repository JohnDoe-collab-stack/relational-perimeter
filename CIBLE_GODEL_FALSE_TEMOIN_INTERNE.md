# Cible scientifique : le `False` de fermeture comme témoin de l'obstruction gödelienne interne

## Statut du document

Ce document fixe la cible scientifique à atteindre. Il ne constitue ni une
preuve de cette cible, ni une affirmation qu'elle est déjà satisfaite par le
code actuel, ni une modification des fondations de `Relational Perimeter`.

La réalisation de Heyting Arithmetic (HA) peut établir la non-vacuité des
prémisses arithmétiques, mais HA reste une instance du cadre. Elle n'est ni le
cadre lui-même, ni le sujet principal de la cible.

## Cible exacte

Dans une réalisation arithmétisable fidèle du cadre périmétral, montrer que le
`False` produit par la tentative de réintégrer la continuation positive dans le
même régime totalisant se factorise, dans la métathéorie Lean, par l'obstruction
portée par une phrase diagonale de Gödel construite et représentée à l'intérieur
du système arithmétique.

Ce `False` doit exprimer uniquement l'échec de la fermeture totalisante. Il ne
doit exprimer ni l'échec du tout constitué, ni l'échec de sa globalité, ni
l'impossibilité de sa continuation.

La chaîne visée est la suivante :

```text
système arithmétique effectif et corrigé
  -> diagonalisation et production interne de G
  -> certification du même G : Truth(G) et (Proof(G) -> Empty)
  -> inscription de cette production et de sa provenance dans une
     présentation périmétrale fidèle
  -> constitution du tout périmétral
  -> continuation positive consommant la production certifiée
  -> tentative d'admission de cette continuation dans le même régime
  -> tentative bilatérale de fermeture
  -> totalisation explicite ou implicite par représentation commune et
     reconstruction
  -> contraction des deux pôles
  -> conversion Truth(G) -> Proof(G), sans contradiction préalable
  -> Empty, puis False pour la conclusion fondationnelle
  -> rejet du régime totalisant, maintien de la continuation constituée
```

Cette cible prolonge la distinction fondationnelle entre complétude
constitutive et exhaustion de la génération : un tout peut être complètement
constitué sans épuiser les continuations que sa propre génération peut encore
produire. La continuation est construite avant que son admission dans l'ancien
régime soit rejetée.

## Obligations formelles

Soient un système arithmétique effectif et corrigé, son exécution diagonale, la
présentation périmétrale fidèle `P` construite avec la production certifiée et
sa continuation canonique stricte `H`. La preuve cible doit établir
conjointement les obligations suivantes.

### 1. Constitution affirmative

La phrase diagonale et sa certification doivent être produites avant leur
inscription dans `P`. Le périmètre doit ensuite être constitué comme tout, puis
`H` doit être effectivement produite comme continuation stricte consommant la
production certifiée. Cette continuation doit fournir des témoins positifs et
ne doit pas être reconstruite après coup à partir d'une contradiction.

### 2. Conservation des distinctions

Toutes les distinctions effectivement établies par la chaîne doivent être
préservées : pôles séparés, identités d'occurrences, positions, statuts, rôles
et provenances. La continuité d'une même détermination à travers les couches
doit être établie par les transports exacts qui la conservent. Elle ne doit pas
être remplacée par une égalité fortuite de valeurs ou par un effacement de
provenance.

Cette obligation n'impose pas que tous les types porteurs soient différents.
Les couches explicite et implicite peuvent employer le même type ; leurs rôles
et leurs occurrences n'en sont pas pour autant identifiés.

### 3. Admission et totalisation fondationnelles inchangées

L'hypothèse principalement réfutée doit être l'admission de la continuation
positive réellement produite dans le même régime. Dans la fondation, une telle
admission est portée conjointement par un `CircularRefinement P H` et par un
témoin `PositiveContinuation refinement.extension`. Le champ `realizesFinal`
du raffinement, appliqué à ce témoin positif, doit produire le
`BilateralClosureAttemptAt` de l'interprétation finale correspondante.

Cette tentative contient les deux totalisations fondationnelles :

```lean
ExplicitTotalization P
ImplicitTotalization P
```

Chacune fournit une représentation commune et une reconstruction qui contracte
les deux pôles. C'est cette chaîne, et non le seul nom d'un type de boucle, qui
doit porter la correspondance recherchée.

`CircularClosureMeaning P H` reste la spécification trajectorielle indépendante
du cadre. Son rejet peut être fourni comme corollaire ou résultat parallèle,
mais il ne suffit pas à lui seul à démontrer la dépendance envers la
représentation commune et sa reconstruction. Une factorisation gödelienne de
ce corollaire exige en plus une loi construite séparément, sans contradiction
préalable :

```text
P.TotalLoop -> (Truth(G) -> Proof(G))
```

Une instance arithmétique doit nécessairement donner un sens concret au champ
abstrait `P.TotalLoop`. Il est permis de le réaliser par une identification
entre les extrémités arithmétiques, y compris entre `Truth(G)` et `Proof(G)`, à
condition de démontrer que cette identification provient fidèlement de la
totalisation fondationnelle sur la même présentation et la même continuation.
Ce qui est interdit est une boucle stipulée et déconnectée des totalisations,
de la continuation effective ou de leur provenance.

### 4. Production interne de la phrase de Gödel

Le codage, l'auto-application, le point fixe et la phrase `G` doivent être
construits par une même exécution arithmétique ordonnée. La certification doit
consommer la production exacte de l'étape précédente. Cette production
certifiée doit ensuite constituer la différence et la provenance de la
présentation périmétrale réalisée. `G` ne doit pas être un témoin étranger
simplement stocké dans une structure après sa construction.

Comme `CircularPresentation` contient déjà le champ négatif
`rejectInitialContraction`, la réalisation concrète doit construire ce champ à
partir de la vérité et de la non-prouvabilité du `G` produit. Elle ne doit pas
le recevoir comme une hypothèse indépendante. La correspondance centrale ne
doit ensuite jamais utiliser ce champ pour fabriquer la conversion
`Truth(G) -> Proof(G)`.

### 5. Raccord exact entre totalisation et complétude au point diagonal

L'admission dans le même régime doit produire la tentative bilatérale réelle ;
une de ses totalisations doit produire la contraction correspondante ; cette
contraction doit ensuite fournir la conversion interdite au point diagonal :

```text
(admission : PositiveSameRegimeAdmission P H)
  -> BilateralClosureAttemptAt (finalInterpretationOf admission)
  -> ExplicitTotalization P ou ImplicitTotalization P
  -> ContractedClosureDifference P
  -> (Truth(G) -> Proof(G))
```

La tentative bilatérale transporte aussi une obstruction dans son attachement.
Pour empêcher que la conclusion soit réintroduite par cette voie, la preuve de
complétude produite doit d'abord projeter uniquement l'une des totalisations,
puis son noyau opérationnel :

```text
BilateralClosureAttemptAt (finalInterpretationOf admission)
  -> ExplicitTotalization P
  -> ExplicitContractionKernel P
```

ou, symétriquement :

```text
BilateralClosureAttemptAt (finalInterpretationOf admission)
  -> ImplicitTotalization P
  -> ImplicitContractionKernel P
```

La contraction et la conversion vers `Truth(G) -> Proof(G)` doivent être
construites depuis les champs positifs de ce noyau. Avant l'obtention de
`Empty`, leurs définitions ne doivent projeter ni
`P.rejectInitialContraction`, ni
`attempt.attachment.obstruction.rejectsContraction`, ni
`ContractedClosureDifference.reject`.

Le raccord arithmétique fidèle doit identifier les deux pôles de la différence
initiale avec les statuts sémantique et syntaxique de la phrase produite, puis
montrer comment la contraction construite induit la fonction dirigée. Ce
passage doit être construit à partir des données positives de la totalisation,
de sa représentation commune et de sa reconstruction. Il ne doit utiliser
auparavant ni `False`, ni `Empty`, ni leurs éliminateurs, ni la réfutation
terminale, ni un champ qui suppose déjà la conclusion.

La provenance doit imposer qu'il s'agit du même `G` que celui produit et
certifié par la chaîne exécutée. Une reconstruction indépendante d'une phrase
extensionnellement égale ne suffit pas.

Une factorisation parallèle partant de `CircularClosureMeaning P H` peut être
conservée si la réalisation fournit la loi
`P.TotalLoop -> (Truth(G) -> Proof(G))` mentionnée plus haut. Cette factorisation
ne remplace pas la factorisation principale par l'admission et la totalisation
fondationnelles.

### 6. Collision gödelienne interne

Le point fixe exact, la représentation du prédicat de preuve et la correction
doivent dériver, pour cette même phrase :

```text
Truth(G)
Proof(G) -> Empty
```

La conversion fournie par la totalisation transforme alors `Truth(G)` en
`Proof(G)`, que la non-prouvabilité réfute. La conclusion gödelienne immédiate
est donc `Empty`. La conclusion fondationnelle dans `Prop` est obtenue par
l'éliminateur constructif `Empty.elim`. La preuve terminale doit avoir la
factorisation causale suivante :

```text
admission fondationnelle de la continuation réelle
  -> tentative bilatérale et totalisation réelle
  -> Truth(G) -> Proof(G)
  -> Empty
  -> False
```

La dérivation de `False` doit réellement passer par cette collision
gödelienne. La juxtaposition d'une réfutation périmétrale indépendante et d'un
théorème d'incomplétude indépendant ne satisfait pas la cible.

« Le même `False` » désigne ici cette identité de chaîne causale, de phrase et
de provenance. Il ne désigne pas une égalité définitionnelle entre un terme de
type `Empty` et un terme de type `False`, ni une égalité de preuves.

### 7. Séparation des dépendances

La preuve et sa documentation doivent distinguer quatre lectures.

- **Formation** : l'exécution arithmétique produit et certifie `G`; cette
  ressource forme la différence et la provenance de `P`; le raffinement et son
  témoin positif forment ensuite l'interprétation finale et la tentative
  bilatérale qui lui est indexée.
- **Exécution** : la totalisation choisie fournit effectivement sa
  représentation commune et sa fonction de reconstruction; l'application de
  cette reconstruction produit la contraction des extrémités.
- **Preuve** : le noyau terminal consomme la contraction, les identifications
  exactes des extrémités avec `Truth(G)` et `Proof(G)`, le témoin de vérité et
  la non-prouvabilité. Il ne doit pas être présenté comme consommant chaque
  donnée transportée par la chaîne si son terme n'en dépend pas.
- **Transport** : la provenance identifie la différence contractée au même
  témoin produit; les égalités d'extrémités transportent la contraction vers
  `Truth(G) = Proof(G)`, puis `Eq.mp` fournit la conversion dirigée.

La chaîne constitutive porte donc davantage que le lemme logique terminal. Ce
surplus doit rester présent dans le résultat global sans être attribué
faussement aux dépendances minimales du dernier lemme.

### 8. Maintien affirmatif après le rejet

La conclusion complète doit conserver simultanément :

```text
tout constitué
+ continuation positive effectivement produite
+ distinctions et provenances préservées
+ impossibilité de l'admission de cette continuation dans le même régime
  totalisant
```

Le résultat négatif porte sur le régime d'admission et sa demande de
totalisation. Il ne porte pas sur l'existence de la continuation.

### 9. Portée générique et non-vacuité concrète

Le théorème central doit être paramétré par les données nécessaires d'un
système arithmétique effectif et corrigé ainsi que par leur raccord fidèle au
cadre périmétral. Il ne doit pas identifier le cadre général à une théorie
arithmétique particulière.

Une instance concrète, telle que HA, doit seulement montrer que ces contrats
peuvent être réalisés sans recevoir la conclusion comme prémisse.

Il n'est pas demandé d'affirmer que toute `CircularPresentation` arbitraire est
gödelienne. Une présentation générale peut ne posséder ni syntaxe arithmétique,
ni codage effectif, ni auto-référence. La conclusion gödelienne vaut pour les
présentations munies du raccord arithmétique fidèle explicité par le théorème.

## Sens rigoureux de « le `False` est le témoin interne de Gödel »

Deux niveaux doivent rester distincts :

- le codage, le prédicat de preuve, la diagonalisation et `G` sont représentés
  dans le langage objet arithmétique ;
- `Truth(G)`, la correction et la fonction qui transforme l'admission supposée
  en `Empty`, puis en `False`, appartiennent à la métathéorie Lean.

La cible ne consiste pas à démontrer `False` dans HA ou dans une autre théorie
correcte. Elle consiste à démontrer, dans Lean, que l'hypothèse supplémentaire
d'admission totalisante, appliquée à une continuation déjà constituée, rencontre
la phrase diagonale construite dans le système objet et produit la contradiction
au niveau métathéorique.

Le mot « interne » impose donc trois conditions :

1. `G` et son prédicat de preuve sont construits ou représentés dans le système
   objet considéré ;
2. l'admission et la totalisation agissent sur cette même production, identifiée
   par sa provenance ;
3. `Empty`, puis le `False` fondationnel, sont obtenus par le point fixe et la
   correction de cette production, et non importés depuis une obstruction sans
   rapport.

Cette internalité est donc relative à la production et à la représentation de
la phrase. Elle n'affirme pas que le système objet dérive sa propre
contradiction.

## Ce que la cible ne demande pas

La cible ne demande pas :

- un théorème d'incomplétude plus fort que celui de Gödel ;
- une preuve que l'architecture périmétrale est l'unique représentation
  possible de l'incomplétude ;
- une séparation générale contre toutes les constructions stagewise ;
- une réfutation de tout shell capable de reproduire des faits terminaux ;
- une identification de la globalité à la totalisation ;
- une preuve que le tout constitué est incomplet au sens constitutif ;
- la seule dérivation de `Truth(G)` et de `Proof(G) -> Empty` ;
- la seule réfutation de `Truth(G) -> Proof(G)` ;
- une boucle arithmétique stipulée sans raccord aux totalisations
  fondationnelles afin de rendre la réfutation immédiate ;
- la promotion de HA du statut d'instance au statut de cadre général.

## Critères de réussite

La cible est atteinte uniquement si toutes les conditions suivantes sont
vérifiées.

1. `G` et sa certification sont produits avant leur inscription dans la
   présentation périmétrale.
2. La continuation stricte consomme cette production et est positivement
   construite avant son rejet par le régime.
3. L'hypothèse consommée est l'admission fondationnelle dans le même régime,
   munie du témoin positif de son extension ; elle produit la tentative
   bilatérale de la même continuation.
4. La tentative consommée contient les `ExplicitTotalization` et
   `ImplicitTotalization` fondationnelles, sans reconstruction indépendante.
5. La preuve projette une totalisation vers son noyau opérationnel et construit
   la complétude produite sans projeter l'obstruction contenue dans `P`, dans
   l'attachement ou dans la différence contractée.
6. Au moins une de ces totalisations construit la contraction qui induit
   `Truth(G) -> Proof(G)` sans consommer de contradiction préalable.
7. `G`, sa vérité, son point fixe et sa non-prouvabilité concernent la même
   production exécutée.
8. La provenance et les occurrences exactes empêchent la substitution d'un
   témoin étranger.
9. La dérivation terminale passe effectivement par `Truth(G) -> Proof(G)`, par
   `Proof(G) -> Empty`, puis par la conversion constructive vers `False`.
10. Les témoins positifs du tout, de la continuation et des distinctions
   effectivement établies restent disponibles dans la conclusion.
11. La réalisation concrète définit `rejectInitialContraction` depuis le témoin
    gödelien produit ; elle ne le reçoit pas comme une hypothèse indépendante.
12. Le théorème générique ne confond pas son interface conditionnelle avec son
    instance arithmétique concrète.
13. Le texte et les preuves distinguent explicitement formation, exécution,
    preuve et transport.
14. Le texte canonique annonce exactement cette portée et n'attribue pas au
    lemme terminal une dépendance constitutive qu'il ne consomme pas.

## Critères d'échec

La cible n'est pas atteinte si l'un des procédés suivants remplace la chaîne
exigée :

- définir `TotalLoop` comme une égalité entre `Truth(G)` et `Proof(G)` sans
  démontrer que cette interprétation réalise fidèlement la totalisation
  fondationnelle ;
- prouver uniquement que Gödel interdit cette boucle, sans passer par la
  tentative bilatérale et ses reconstructions ;
- utiliser l'obstruction fondationnelle déjà disponible pour fabriquer par
  élimination n'importe quelle conséquence gödelienne ;
- projeter l'obstruction portée par l'attachement de la tentative au lieu de
  passer par le noyau positif de la totalisation ;
- recevoir `rejectInitialContraction`, la complétude produite ou le rejet de la
  fermeture comme champ opaque du raccord dit fidèle ;
- choisir une interprétation finale indépendamment du raffinement et du témoin
  positif qui la constituent ;
- transporter un `G` construit indépendamment dans le périmètre ;
- produire deux phrases extensionnellement égales sans identité de provenance ;
- conserver la production gödelienne comme champ sans la consommer dans la
  fermeture ;
- conclure seulement `Truth(G) ∧ ¬Proof(G)` ;
- conclure seulement que HA est incomplète ;
- perdre la continuation positive lors du passage à `Empty` puis à `False` ;
- interpréter `False` comme l'incohérence du système arithmétique plutôt que
  comme la réfutation de l'hypothèse supplémentaire de totalisation.

## Forme minimale du résultat recherché

La surface publique finale doit exposer, pour une même réalisation, au moins
les données suivantes :

```text
producedDiagonalSentence
exactFixedPoint
producedTruth
producedUnprovability
faithfulPerimetralRealization
positiveWhole
strictContinuation
finalInterpretationOf
positiveSameRegimeAdmission
sameRegimeAdmissionToBilateralAttempt
admissionToExplicitContractionKernel
totalizationKernelToProducedCompleteness
rejectSameRegimeAdmissionThroughProducedCompleteness
```

Le cœur logique attendu est :

```text
PositiveSameRegimeAdmission P H :=
  Σ refinement : CircularRefinement P H,
    PositiveContinuation refinement.extension

finalInterpretationOf
    (admission : PositiveSameRegimeAdmission P H) :=
  finalClosureInterpretation
    (finalBoundaryOccurrence admission.1.toLabelled admission.2)

sameRegimeAdmissionToBilateralAttempt :
  (admission : PositiveSameRegimeAdmission P H)
    -> BilateralClosureAttemptAt (finalInterpretationOf admission)

admissionToExplicitContractionKernel :
  PositiveSameRegimeAdmission P H
    -> ExplicitContractionKernel P

totalizationKernelToProducedCompleteness :
  ExplicitContractionKernel P
    -> (Truth(G) -> Proof(G))

rejectSameRegimeAdmissionThroughProducedCompleteness :
  PositiveSameRegimeAdmission P H -> False
```

`faithfulPerimetralRealization` est ici un nom de travail, pas une prémisse
opaque autorisée à contenir la conclusion. Ses données négatives doivent être
limitées à la non-prouvabilité de `G` déjà dérivée par l'exécution diagonale.
Son raccord périmétral doit exposer seulement les identifications positives de
la production, de la différence, de la provenance et des deux pôles avec
`Truth(G)` et `Proof(G)`. Il ne peut recevoir comme champs ni
`Truth(G) -> Proof(G)`, ni un rejet de totalisation, ni un rejet de fermeture.

`admissionToExplicitContractionKernel` doit être la composition visible de
`sameRegimeAdmissionToBilateralAttempt`, de la projection
`explicitTotalization` et de `ExplicitTotalization.toContractionKernel`. La
version implicite doit suivre la projection symétrique. Ces définitions rendent
contrôlable l'absence d'accès à l'obstruction stockée dans l'attachement.

La dernière déclaration doit produire l'interprétation et la tentative
bilatérale depuis la même admission, en extraire la totalisation explicite et
son noyau opérationnel, construire la contraction depuis ce noyau, appliquer la
conversion obtenue à la vérité produite de `G`, appliquer ensuite la
non-prouvabilité au certificat obtenu, puis convertir l'`Empty` résultant en
`False`. Une variante entièrement symétrique peut employer le noyau implicite.

Une déclaration séparée peut établir en outre :

```text
totalLoopToProducedCompleteness :
  P.TotalLoop -> (Truth(G) -> Proof(G))

rejectTrajectoryClosureThroughProducedCompleteness :
  CircularClosureMeaning P H -> False
```

La seconde déclaration n'est admissible par la voie gödelienne que si la
première a d'abord été construite sans utiliser l'obstruction. Elle ne remplace
pas le résultat principal sur l'admission dans le même régime, puisqu'elle ne
consomme pas nécessairement la tentative bilatérale et ses totalisations.

Cette signature est indicative : les noms peuvent différer. En revanche, sa
direction causale, l'identité des ressources consommées et l'indépendance de la
constitution positive sont obligatoires.

## Contribution scientifique visée

La contribution recherchée n'est pas un renforcement du théorème classique de
Gödel. Elle est une interprétation formelle et constitutive de son obstruction :

> Une phrase de Gödel construite et représentée dans le système objet permet de
> démontrer, dans la métathéorie, pourquoi une fermeture totalisante échoue au
> moment où le régime tente de réabsorber une continuation positivement
> constituée par une représentation commune et une même reconstruction : cette
> totalisation contracte une distinction que la chaîne a préservée.

Le progrès éventuel porte donc sur l'explicitation formelle de la chaîne, des
porteurs, des occurrences, des provenances et du changement de régime. Il ne
porte pas sur la découverte d'un nouveau théorème d'incomplétude.

## Sources de cadrage

- [Relations primitives et constitution du périmètre](docs/relations-primitives-constitution-perimetre.fr.md)
- [Procédure de travail scientifique](docs/methode-de-travail-scientifique.fr.md)
- [`CircularPresentation` et `CircularClosureMeaning`](StrongPerimetralTurning.lean)
