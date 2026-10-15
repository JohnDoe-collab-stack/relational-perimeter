# Énoncé formel stable — obstruction gödelienne de la fermeture totalisante

Soit `S` une réalisation de `EffectivelyPresentedSoundGodelSystem`, et posons :

```text
E := effectiveGodelExecution S
G := E.witness.production.sentence
P := godelPerimetralPresentation E
H := godelPerimetralContinuation E
Admission(E) := GodelPositiveSameRegimeAdmission E
```

Dans ce document, les notations suivantes abrègent uniquement les types Lean
exacts :

```text
Truth(X) := S.toGodelInterpretation.Truth X
Proof(X) := S.toGodelSyntax.Proof X
Whole(P) := ExactPerimeterRealization P (perimeterDeployment P)
StrictContinuation(P, H) :=
  StrictConstitutivePrefix (perimeterDeployment P) H
```

`Truth(G)`, `Proof(G)`, `Whole(P)` et `StrictContinuation(P, H)` sont des types
Lean, et non les membres d'une conjonction propositionnelle artificielle. La
formalisation construit des habitants de `Truth(G)`, `Whole(P)` et
`StrictContinuation(P, H)`, ainsi qu'une fonction `Proof(G) → Empty`. Elle ne
construit un habitant de `Proof(G)` que sous l'hypothèse ultérieure d'un terme
`Admission(E)`.

## 1. Production gödelienne exécutée

La chaîne suivante produit un seul et même énoncé `G` :

```text
diagonalisation → auto-application → certification
```

Elle construit exactement :

```text
G = godelSentence S.toGodelSyntax S.unprovabilityFormula

S.toGodelSyntax.ProvableIff G
  (S.toGodelSyntax.substitute S.unprovabilityFormula
    (S.toGodelSyntax.quoteSentence G))

Truth(G)
Proof(G) → Empty
```

Le deuxième type est le point fixe formel. Les lois de représentation de `S`
interprètent la phrase substituée comme l'absence de preuve de `G` ; elles
permettent ensuite de construire séparément la vérité de `G` et la fonction
`Proof(G) → Empty`. L'énoncé informel « `G` dit qu'il n'est pas prouvable »
résume cette chaîne, mais ne remplace pas son type exact.

La production est portée par une histoire ordonnée. Elle possède des
occurrences distinctes pour la diagonalisation, l'auto-application et la
certification :
[`ExecutedGodelProduction.occurrences`](RelationalPerimeter/Constitution/Godel/Diagonal.lean).

## 2. Constitution affirmative

Le témoin exécuté de `G` constitue la différence initiale et la provenance de
`P`. Le cadre construit ensuite des habitants de :

```text
Whole(P)
StrictContinuation(P, H)
```

La continuation possède une occurrence nouvelle, distincte des occurrences de
production et de certification. Sa ressource source, lue au nœud frontière,
est `.continued E.witness` ; son payload est le témoin certifié qui porte la
phrase `G`. Elle conserve ce témoin exécuté et sa provenance exacte :
[`GodelAffirmativeConstitution`](RelationalPerimeter/Constitution/Godel/PerimetralCorrespondence.lean).

L'histoire d'exécution gödelienne — diagonalisation, auto-application,
certification — et l'histoire périmétrale — production, certification,
continuation — sont deux systèmes d'occurrences distincts. Leur correspondance
est portée par l'identité de la production, de la ressource et du témoin. Le
document ne revendique pas une identité littérale entre les occurrences de ces
deux histoires.

Ces données positives sont construites avant toute hypothèse de réadmission ou
de fermeture.

L'ordre constitutif démontré est donc :

```text
production et certification de G
  → constitution affirmative de P
  → continuation effective H
  → hypothèse ultérieure d'Admission(E)
  → tentative bilatérale
  → totalisation et contraction
  → Empty
  → False
```

## 3. Hypothèse de réadmission dans le même régime

L'admission considérée est exactement :

```text
Admission(E) :=
  Σ R : CircularRefinement P H,
    PositiveContinuation R.extension
```

Un terme `admission : Admission(E)` contient donc un raffinement précis et le
témoin positif de sa continuation. Depuis ce même terme :

```text
godelFinalInterpretationOf admission
```

construit l'interprétation finale, puis :

```text
godelBilateralClosureAttemptOf admission :
  BilateralClosureAttemptAt (godelFinalInterpretationOf admission)
```

applique `CircularRefinement.realizesFinal` au témoin positif fourni par cette
admission. La tentative bilatérale n'est ni reconstruite indépendamment, ni
supposée séparément.

## 4. Totalisation et conversion vérité–preuve

La tentative bilatérale contient deux totalisations positives. Elles donnent
les deux chemins suivants.

### Voie explicite

```text
Admission(E)
  → BilateralClosureAttemptAt
  → ExplicitTotalization P
  → ExplicitContractionKernel P
  → Truth(G) → Proof(G)
```

### Voie implicite

```text
Admission(E)
  → BilateralClosureAttemptAt
  → ImplicitTotalization P
  → ImplicitContractionKernel P
  → Truth(G) → Proof(G)
```

Dans `P`, les extrémités sont exactement :

```text
leftEndpoint  = Truth(G)
rightEndpoint = Proof(G)
```

Chaque noyau reconstruit ces deux extrémités depuis une représentation commune
et fournit leur égalité. Le transport le long de cette égalité construit alors
la conversion dirigée :

```text
Truth(G) → Proof(G)
```

Cette conversion consomme le noyau positif et les identifications positives des
extrémités de `P`. Elle ne consulte ni `rejectInitialContraction`, ni une
obstruction d'attachement, ni un rejet de différence contractée, ni
`Proof(G) → Empty`, ni un terme de type `Empty` ou `False` :
[`godelExplicitKernelToProducedCompleteness`](RelationalPerimeter/Constitution/Godel/PerimetralCorrespondence.lean)
et
[`godelImplicitKernelToProducedCompleteness`](RelationalPerimeter/Constitution/Godel/PerimetralCorrespondence.lean).

Ici, « ne consulte pas » signifie qu'aucune projection vers ces champs
négatifs n'est exécutée. Les constantes qui les construisent restent présentes
dans l'indice de type `P`, puisque `godelCircularPresentation` contient la
présentation complète ; elles ne sont pas lues par la conversion.

La dépendance doit être distinguée à deux niveaux. La chaîne constitutive
depuis `Admission(E)` consomme le raffinement, son témoin positif exact et
`CircularRefinement.realizesFinal` pour obtenir la tentative bilatérale. Une
fois une totalisation projetée depuis cette tentative, le sous-terme qui
construit `Truth(G) → Proof(G)` dépend de cette totalisation de `P` et ne relit
plus les données propres de `H`. Cette dépendance logique minimale ne remplace
ni la constitution de `H`, ni l'admission indexée par `P` et `H`, ni le chemin
de réalisation effectivement suivi.

## 5. Collision gödelienne et ordre de dérivation

Pour chaque voie, la conversion obtenue est appliquée à la vérité déjà produite
du même `G` :

```text
Truth(G) → Proof(G)
Truth(G)
→ Proof(G)
```

La non-prouvabilité certifiée du même `G` est appliquée seulement ensuite :

```text
Proof(G)
Proof(G) → Empty
→ Empty
```

Enfin, et seulement à cette dernière étape, `Empty.elim` fournit `False`.

La voie explicite est donc :

```text
Admission(E)
  → BilateralClosureAttemptAt
  → ExplicitTotalization P
  → ExplicitContractionKernel P
  → Truth(G) → Proof(G)
  → Truth(G)
  → Proof(G)
  → Proof(G) → Empty
  → Empty
  → False
```

La voie implicite est symétrique :

```text
Admission(E)
  → BilateralClosureAttemptAt
  → ImplicitTotalization P
  → ImplicitContractionKernel P
  → Truth(G) → Proof(G)
  → Truth(G)
  → Proof(G)
  → Proof(G) → Empty
  → Empty
  → False
```

Les déclarations terminales sont :

```text
rejectGodelExplicitAdmissionToEmpty : Admission(E) → Empty
rejectGodelImplicitAdmissionToEmpty : Admission(E) → Empty

rejectGodelExplicitSameRegimeAdmission : Admission(E) → False
rejectGodelImplicitSameRegimeAdmission : Admission(E) → False
```

## 6. Résultat formel complet

Le résultat complet n'est pas une conjonction propositionnelle artificielle.
Il est l'habitant suivant d'une structure dépendante :

```text
executedGodelPerimetralCorrespondence E :
  ExecutedGodelPerimetralCorrespondence E
```

Cette structure contient simultanément :

```text
producedTruth : Truth(G)
producedUnprovability : Proof(G) → Empty
positiveWhole : Whole(P)
strictContinuation : StrictContinuation(P, H)
explicitAdmissionRejected : Admission(E) → False
implicitAdmissionRejected : Admission(E) → False
```

Elle contient aussi l'identité exacte de la phrase produite, son point fixe, la
construction de `P` depuis le même témoin, les occurrences ordonnées, la
provenance, l'interprétation finale de chaque admission, la tentative
bilatérale correspondante et les conversions explicite et implicite
`Truth(G) → Proof(G)`.

La phrase `G` est canonique pour le système et la formule de non-prouvabilité
fixés. Cette identité de phrase n'affirme pas l'unicité de tous les records
`ExecutedGodelWitness`. Chaque présentation `P` demeure toutefois indexée par
son témoin exécuté exact et par la provenance qui le retient.

Le témoin constructif de l'impossibilité de fermeture est donc chacune des
fonctions :

```text
Admission(E) → False
```

La formalisation ne construit pas un terme de type `False` sans hypothèse. Elle
montre que toute tentative d'habiter `Admission(E)` produit la collision
gödelienne puis `False`.

## 7. Schème générique et spécificité gödelienne

La forme logique terminale de l'obstruction est générique :

```text
A
A → B
B → Empty
→ Empty
```

Dans la présentation gödelienne, le contenu d'un noyau explicite de contraction
est exactement interconvertible avec l'égalité de types :

```text
Truth(G) = Proof(G)
```

Une projection ou une identification abstraite peut donc reproduire cette
forme terminale. La spécificité gödelienne ne réside pas dans la seule forme de
la contraction, mais dans la chaîne exécutée qui en produit intérieurement les
deux pôles :

```text
diagonalisation interne
  → production du même G
  → certification de Truth(G)
  → certification de Proof(G) → Empty
  → constitution de P depuis ce témoin exécuté
  → continuation effective H avec occurrences et provenance conservées
  → admission de H dans le même régime
  → tentative portant une totalisation de P
  → contraction de Truth(G) et Proof(G)
  → Empty
```

Une projection abstraite peut représenter l'identification terminale. Elle ne
construit pas, à elle seule, cette généalogie gödelienne, l'identité de la même
phrase `G`, les histoires ordonnées, la provenance conservée ni l'admission
indexée par l'exécution exacte `E`.

Le résultat établit ainsi que Gödel réalise intérieurement, effectivement et
de manière traçable, ce schème constitutif général. Il n'affirme ni que ce
schème est réservé à Gödel, ni qu'aucune autre présentation mathématique de
l'incomplétude n'est possible. La généricité de la contraction relève de la
portée générale du cadre ; elle ne remplace pas la spécificité de la production
gödelienne qui en fournit les pôles.

## 8. Portée générique et instance HA

Le résultat précédent vaut pour toute réalisation de
`EffectivelyPresentedSoundGodelSystem`. Il constitue la correspondance
gödelienne générique à l'intérieur du cadre. L'interface fixe les contrats
nécessaires à cette correspondance ; son seul nom ne transforme pas chacun de
ses habitants en théorie arithmétique. Le caractère arithmétique d'une
réalisation concrète doit être fermé par cette réalisation.

Séparément :

```text
heytingArithmeticEffectiveGodelSystem :
  EffectivelyPresentedSoundGodelSystem
```

ferme concrètement les contrats effectifs et sémantiques avec la syntaxe, les
codages, le vérificateur booléen de preuves, le point fixe interne, la correction
et la représentation de la non-prouvabilité de HA. Puis :

```text
heytingArithmeticGodelPerimetralCorrespondence
```

instancie le résultat générique. HA établit ainsi la non-vacuité concrète du
cadre ; HA demeure une instance du cadre et n'est pas le cadre lui-même.

## Conclusion formelle

La formalisation établit positivement :

> Un tout peut être complètement constitué et produire une continuation
> effective tout en étant incapable de l'admettre dans son régime totalisant
> initial au sens exact de `Admission(E)`, parce que toute telle admission
> réalise une tentative portant une totalisation de `P` qui contracte
> `Truth(G)` et `Proof(G)`.

L'incomplétude reçoit alors son explication structurelle :

> La continuation existe positivement. Ce qui échoue est uniquement son
> admission totalisante dans le même régime : la tentative alors réalisée
> contracte la distinction constitutive entre vérité et preuve.

Les fonctions `Admission(E) → False` témoignent de cette impossibilité de
fermeture. Elles ne réfutent ni le tout, ni sa constitution, ni sa continuation.

## Engagement signé

Je signe cet énoncé comme formulation scientifique de référence de notre
travail sur la correspondance entre Gödel et le tournant périmétral.

Je m'engage à :

- maintenir cette cible exacte sans lui substituer un résultat voisin ;
- ne pas réduire la contribution aux seuls témoins `Truth(G)` et
  `Proof(G) → Empty` ;
- conserver la constitution affirmative, la continuation effective et leur
  provenance dans toute présentation du résultat ;
- maintenir les deux factorisations causales complètes par la réadmission, la
  tentative bilatérale, la totalisation, la contraction, la conversion
  `Truth(G) → Proof(G)`, `Empty`, puis `False` ;
- distinguer la chaîne constitutive complète de la dépendance logique minimale
  du sous-terme terminal, sans supprimer `H` de la formation de l'admission ;
- distinguer la généricité de la contraction terminale de la spécificité de la
  production gödelienne qui en fournit intérieurement les deux pôles ;
- ne jamais présenter un terme `Admission(E) → False` comme l'échec du tout ou
  de sa continuation ;
- maintenir HA dans son rôle d'instance du cadre, jamais comme le cadre
  lui-même.

**Signé : Codex — 16 octobre 2026**
