# Plan d’implémentation minimal : témoin gödelien interne du `False` de fermeture

## Statut et autorité

Ce document est un plan de chantier. Il organise l’implémentation de la cible
fixée dans
[`CIBLE_GODEL_FALSE_TEMOIN_INTERNE.md`](CIBLE_GODEL_FALSE_TEMOIN_INTERNE.md),
sans la modifier, l’affaiblir ni lui substituer une ancienne cible d’audit.

La cible reste autoritaire en cas d’écart. Ce plan ne constitue ni une preuve,
ni une affirmation scientifique, ni une autorisation de commiter, pousser,
fusionner ou lancer un audit extérieur.

## Décisions fermes de périmètre

1. `StrongPerimetralTurning.lean` reste inchangé.
2. Le résultat central est générique ; HA n’est qu’une instance de non-vacuité.
3. La preuve principale part de l’admission de la continuation réellement
   produite et passe par `CircularRefinement.realizesFinal`, une totalisation
   fondationnelle et son noyau positif.
4. Le rejet ne part ni de `CircularClosureMeaning`, ni de
   `P.rejectInitialContraction`, ni de l’obstruction contenue dans
   `BilateralClosureAttemptAt`.
5. Une seule réalisation arithmétique concrète est intégrée.
6. Aucun système-jouet, séparation E1, progression de théories, construction
   stagewise, seconde instance HA ou diagnostic latéral n’entre dans le lot.
7. Aucun ancien commit volumineux n’est repris globalement. Une source
   antérieure ne peut être réutilisée qu’après lecture de ses énoncés complets
   et justification de chacune de ses dépendances.

## Surface de fichiers visée

Le noyau nouveau doit tenir dans deux modules Lean.

### 1. Production arithmétique générique

`RelationalPerimeter/Constitution/Godel/Diagonal.lean`

Responsabilités exclusives :

- interface effective et corrigée du système arithmétique ;
- codage, diagonalisation, auto-application et point fixe ;
- relation de preuve vérifiée et vérité sémantique ;
- exécution ordonnée de la production ;
- certification du même énoncé produit ;
- construction de `Truth(G)` et de `Proof(G) → Empty`.

Ce module ne définit aucune présentation périmétrale, aucune totalisation et
aucun rejet de régime.

### 2. Correspondance périmétrale

`RelationalPerimeter/Constitution/Godel/PerimetralCorrespondence.lean`

Responsabilités exclusives :

- ressources périmétrales typées issues de la production certifiée ;
- présentation circulaire fidèle construite depuis cette production ;
- tout constitué, occurrences exactes et continuation positive ;
- admission dépendante dans le même régime ;
- tentative bilatérale obtenue par la fondation ;
- extraction des noyaux de contraction ;
- conversion `Truth(G) → Proof(G)` ;
- `Empty`, puis `False`, par le témoin gödelien produit ;
- paquet final conservant les données affirmatives.

### 3. Instance concrète séparée

`RelationalPerimeter/Instances/HeytingArithmetic/Godel.lean`

Ce module instancie l’interface générique. Ses éventuels modules auxiliaires
restent sous `RelationalPerimeter/Instances/HeytingArithmetic/`. Aucun de ces
modules ne doit être importé par les deux modules génériques précédents.

La liste exacte des auxiliaires ne sera fixée qu’après audit de dépendances.
Chaque auxiliaire devra fermer une obligation explicite de l’interface ; un
fichier sans consommateur nécessaire sera exclu.

### 4. Contrôles

- `Tests/GodelPerimetralCorrespondenceRegression.lean` ;
- `Tests/HeytingArithmeticGodelInstanceRegression.lean` ;
- au plus trois fixtures ciblées sous `Tests/ExpectedFailure/`, uniquement si
  elles contrôlent une substitution réellement interdite par les types.

Un seul document scientifique final et une seule entrée de registre seront
créés après la preuve. Aucun ancien document Gödel ne sera réintroduit.

## Phase 0 — figer le contrat avant le code

### Travail

- conserver comme base `origin/main` au SHA
  `f13930ce2eb3a338c6cd26b4bb686a152e7f152b`, depuis lequel la branche a été
  créée ;
- garder le diff initial limité au document cible et au présent plan ;
- relever les types fondationnels complets qui seront consommés :
  `CircularPresentation`, `ExplicitTotalization`, `ImplicitTotalization`,
  `ExplicitContractionKernel`, `ImplicitContractionKernel`,
  `ContractedClosureDifference`, `PositiveContinuation`,
  `FinalClosureInterpretation`, `BilateralClosureAttemptAt` et
  `CircularRefinement` ;
- consigner qu’aucune entrée Gödel n’existe encore dans le registre de `main`.

### Gate

Ne commencer aucun module Lean si une étape envisagée exige de modifier une
définition fondationnelle. Dans ce cas, arrêter et signaler l’incompatibilité
avec la cible au lieu de déplacer le contrat.

## Phase 1 — interface gödelienne sans conclusion prémissée

### Construction

Définir une interface effective minimale contenant seulement les données et
lois nécessaires :

- types des formules unaires et des phrases ;
- codages naturels et décodages avec lois de retour ;
- substitution numérique et diagonalisation exécutables ;
- vérificateur booléen de preuves ;
- vérificateur booléen des certificats d’équivalence ;
- transport avant et arrière des preuves le long d’une équivalence certifiée ;
- `Truth : Sentence → Type` ;
- correction `Proof(sentence) → Truth(sentence)` ;
- formule d’improuvabilité et ses deux directions de représentation.

Les champs suivants sont interdits dans l’interface :

- un énoncé diagonal déjà choisi ;
- `Truth(G)` ou `Proof(G) → Empty` pour le futur `G` ;
- `Truth(G) → Proof(G)` ;
- un rejet de totalisation, de raffinement ou de fermeture ;
- une présentation périmétrale déjà équipée de sa conclusion.

### Résultat attendu

L’interface doit permettre de définir constructivement `Proof(sentence)` comme
un code accompagné du résultat positif du vérificateur. Les décodeurs doivent
donner l’injectivité requise sans `Classical` ni quotient opaque.

### Gate

Lire chaque champ en distinguant formation, exécution, preuve et transport.
Refuser l’interface si la conclusion cible peut être obtenue directement depuis
un de ses champs sans exécuter la diagonalisation.

## Phase 2 — production et certification exécutées du même `G`

### Construction

Créer une chaîne de données dépendantes :

```text
formule d’improuvabilité reçue
  -> formule diagonalisée
  -> auto-application produisant la phrase G
  -> certificat exact du point fixe
  -> témoin certifié contenant le même G
```

Les structures de sortie doivent conserver leur producteur immédiat. Une
histoire typée doit exposer au minimum les occurrences distinctes de
diagonalisation, d’auto-application et de certification, avec leur ordre.

Le témoin certifié expose :

```text
production
exactFixedPoint
producedTruth
producedUnprovability
```

`producedTruth` et `producedUnprovability` sont dérivés du point fixe, de la
correction et de la représentation. Ils ne sont pas fournis à l’exécution.

### Gate

- la certification reçoit exactement la production précédente ;
- la phrase du point fixe est définitionnellement ou propositionnellement la
  phrase portée par cette production ;
- aucune continuation ni contradiction périmétrale n’intervient ici ;
- les déclarations publiques du module ont un bloc `AXIOM_AUDIT` unique et
  sans axiome.

## Phase 3 — construire la présentation fidèle depuis le témoin

### Ressources positives

Définir un type de ressources périmétrales avec seulement les états utiles :

```text
produced production
certified witness
continued witness
```

Définir les compatibilités dirigées :

```text
produced -> certified
certified -> continued
continued -> produced
```

Les constructeurs doivent recevoir les valeurs exactes produites par la chaîne
de la phase 2. Aucune reconstruction indépendante de `G` n’est admise.

### Présentation

Définir directement `godelCircularPresentation witness` avec :

- `Difference :=` le type du témoin exécuté ;
- `initialNode.difference := witness` ;
- `Provenance candidate := PLift (candidate = witness)` ;
- `leftEndpoint := Truth(witness.production.sentence)` ;
- `rightEndpoint := Proof(witness.production.sentence)` ;
- pôles gauche et droit indexés par la phrase de chaque candidat ;
- `TotalLoop` interprété concrètement, puis raccordé aux extrémités ;
- `rejectInitialContraction` construit dans la définition depuis
  `witness.producedTruth` et `witness.producedUnprovability`.

`rejectInitialContraction` est nécessaire pour satisfaire
`CircularPresentation`, mais aucune preuve centrale ultérieure ne doit le
projeter.

### Provenance et occurrences

Prouver séparément :

- que la différence initiale est exactement le témoin produit ;
- que toute provenance de cette différence retient cette identité ;
- que les occurrences périmétrales de production et de certification sont
  distinctes et ordonnées ;
- qu’elles portent respectivement la production et la certification extraites
  de l’histoire exécutée ;
- que leur identité d’occurrence n’est jamais remplacée par l’égalité de leurs
  charges utiles.

### Gate

Un témoin étranger, même porteur d’une phrase extensionnellement égale, doit
être inutilisable sans transport explicite de provenance.

## Phase 4 — constituer le tout et la continuation avant tout rejet

### Construction

À partir de `P := godelCircularPresentation witness`, construire :

- le déploiement exact du périmètre ;
- le témoin positif du tout constitué
  `ExactPerimeterRealization P (perimeterDeployment P)` ;
- `H := oneStepAfterPerimeter P` ;
- `oneStepFaithfullyLabelledExtension P` ;
- `oneStepAfterPerimeter_positiveContinuation P` ;
- le `StrictConstitutivePrefix` correspondant ;
- les occurrences ancienne de production, ancienne de certification et
  nouvelle de continuation, avec leurs séparations.

Le paquet final ne stocke pas `StrongPerimetralTurningCertificate`, car cette
structure contient aussi des fonctions de rejet inutiles à la constitution
affirmative. Les constructeurs positifs fondationnels sont appelés directement.

### Consommation à démontrer

Le résultat global doit montrer que `H` est formé depuis la présentation déjà
indexée par le témoin certifié. La ressource finale et le registre de provenance
de l’interprétation doivent pointer vers cette même différence initiale.

Exposer en particulier le pas généré exact de `H` : sa source porte la ressource
`continued witness`, sa cible porte la ressource `produced witness.production`
et sa compatibilité est le constructeur `continuationToProduction` de ce même
témoin. Cette lecture empêche de réduire la consommation à la simple présence
du témoin dans un champ de la présentation.

### Gate

À la fin de cette phase, tous les témoins affirmatifs existent, mais aucune
hypothèse d’admission et aucun `False` n’ont été introduits.

## Phase 5 — former l’admission dépendante exacte

Définir, pour la présentation et la continuation déjà construites :

```lean
abbrev PositiveSameRegimeAdmission
    (P : CircularPresentation)
    (H : RootedGeneratedHistory P) : Type _ :=
  Σ refinement : CircularRefinement P H,
    PositiveContinuation refinement.extension
```

Puis définir exactement :

```text
finalInterpretationOf admission
sameRegimeAdmissionToBilateralAttempt admission
```

La première définition emploie :

```text
finalClosureInterpretation
  (finalBoundaryOccurrence admission.1.toLabelled admission.2)
```

La seconde est l’application visible de :

```text
admission.1.realizesFinal admission.2
```

### Gate

- l’interprétation finale n’est jamais choisie indépendamment ;
- la tentative est indexée par l’interprétation formée depuis la même admission ;
- une continuation positive seule ne peut pas être présentée comme une
  admission ; le raffinement reste requis.

## Phase 6 — extraire uniquement les données positives de totalisation

Définir deux projections courtes :

```text
admissionToExplicitContractionKernel
admissionToImplicitContractionKernel
```

La voie explicite doit être exactement la composition :

```text
admission
  -> sameRegimeAdmissionToBilateralAttempt
  -> .explicitTotalization
  -> ExplicitTotalization.toContractionKernel
```

La voie implicite utilise symétriquement `.implicitTotalization` et
`ImplicitTotalization.toContractionKernel`.

### Interdictions contrôlées

Ces définitions ne doivent accéder ni à :

- `.attachment` ;
- `.obstruction` ;
- `.rejectsContraction` ;
- `P.rejectInitialContraction` ;
- `ContractedClosureDifference.reject` ;
- `explicitTotalizationRejected` ou `implicitTotalizationRejected` ;
- un éliminateur de `False` ou d’`Empty`.

### Gate

Lire les corps complets de ces définitions. Un type correct ou un build vert ne
suffit pas : la composition ci-dessus doit être visible dans le terme.

## Phase 7 — construire la complétude produite sans contradiction préalable

Définir :

```text
explicitKernelToProducedCompleteness
implicitKernelToProducedCompleteness
```

Chaque fonction reçoit uniquement le noyau correspondant, indexé par
`godelCircularPresentation witness`, puis :

1. construit la contraction avec
   `explicitKernelContractsClosureDifference` ou
   `implicitKernelContractsClosureDifference` ;
2. extrait seulement l’égalité positive des pôles ou des extrémités ;
3. transporte cette égalité le long des identifications exactes avec
   `Truth(G)` et `Proof(G)` ;
4. retourne `Truth(G) → Proof(G)` par `Eq.mp`.

Construire en outre, depuis la même égalité positive des extrémités, les deux
lemmes de fidélité suivants :

```text
explicitKernelToTotalLoop
implicitKernelToTotalLoop
```

Ils appliquent uniquement `P.closeFromIdentification` à l’égalité obtenue. Ils
établissent que le sens concret choisi pour `P.TotalLoop` est bien produit par
les totalisations fondationnelles. Ils ne sont pas utilisés pour remplacer la
factorisation principale par l’admission et les noyaux.

La provenance appartient à la formation de la contraction et le type de la
présentation reste indexé par le témoin produit. Le lemme terminal ne doit pas
être décrit comme consommant la provenance s’il n’en projette pas le champ.

### Gate

Les deux fonctions doivent compiler alors que leur corps ne contient aucun des
noms négatifs interdits à la phase 6. Cette vérification est sémantique et
textuelle, pas seulement syntaxique.

## Phase 8 — produire `Empty`, puis `False`, par la collision interne

Définir d’abord une conclusion dans `Type` :

```text
rejectSameRegimeAdmissionToEmpty
  : PositiveSameRegimeAdmission P H -> Empty
```

Son corps suit obligatoirement cet ordre :

```text
admission
  -> tentative bilatérale
  -> totalisation explicite
  -> noyau explicite
  -> Truth(G) -> Proof(G)
  -> application à producedTruth
  -> Proof(G)
  -> application de producedUnprovability
  -> Empty
```

Définir ensuite seulement :

```text
rejectSameRegimeAdmissionThroughProducedCompleteness
  : PositiveSameRegimeAdmission P H -> False
```

par `Empty.elim` appliqué au résultat précédent.

La variante implicite peut être fournie comme contrôle symétrique, mais un seul
chemin est désigné comme preuve canonique afin de ne pas dupliquer le résultat
scientifique.

### Gate

Le graphe des appels de la preuve canonique doit passer par la fonction de
complétude construite à la phase 7. Tout appel direct à un rejet fondationnel
fait échouer la phase.

## Phase 9 — paquet affirmatif final

Construire un unique résultat générique exposant au moins :

```text
producedDiagonalSentence
exactFixedPoint
producedTruth
producedUnprovability
faithfulPerimetralRealization
positiveWhole
strictContinuation
finalInterpretationOf
sameRegimeAdmissionToBilateralAttempt
admissionToExplicitContractionKernel
explicitKernelToProducedCompleteness
rejectSameRegimeAdmissionThroughProducedCompleteness
```

Le paquet conserve également les occurrences et provenances établies aux
phases 3 et 4. Il ne contient pas une admission : il contient la fonction qui
réfute toute admission de la continuation construite dans le même régime.

### Séparation des dépendances à documenter

- **Formation** : production certifiée, présentation, occurrences,
  continuation, admission dépendante et interprétation finale.
- **Exécution** : représentation commune, reconstruction et contraction
  effectivement fournies par le noyau extrait.
- **Preuve** : égalité des extrémités, vérité du même `G` et non-prouvabilité.
- **Transport** : indexation par le même témoin, égalités des pôles et `Eq.mp`.

### Gate

Le paquet doit conserver le tout et la continuation même lorsque la fonction
de rejet est présente. La conclusion négative porte uniquement sur l’admission
totalisante.

## Phase 10 — tests adversariaux minimaux

### Test positif principal

`Tests/GodelPerimetralCorrespondenceRegression.lean` vérifie :

- les types exacts de chaque déclaration publique de la phase 9 ;
- l’identité de la phrase entre production, certification et présentation ;
- l’ordre et la distinction des occurrences ;
- l’indexation de l’interprétation et de la tentative par la même admission ;
- les deux extractions de noyau ;
- la factorisation `admission -> Empty -> False` ;
- l’absence d’axiomes de toutes les déclarations testées.

### Échecs attendus autorisés

N’ajouter une fixture que si le compilateur rejette précisément :

1. le remplacement de la production certifiée par un témoin étranger ;
2. l’utilisation d’une continuation positive sans le raffinement requis ;
3. l’utilisation d’une interprétation finale construite depuis une autre
   admission.

Ne pas ajouter de tests Unit, `0 = 0`, shell stagewise, non-factorisation ou
unicité explicative : ils ne contrôlent pas la cible actuelle.

## Phase 11 — réalisation HA, après fermeture du théorème générique

### Ordre obligatoire

1. Auditer en lecture seule les sources HA réutilisables.
2. Établir leur fermeture transitive d’imports depuis l’unique instance nommée.
3. Associer chaque module retenu à un champ précis de l’interface générique.
4. Écarter tout module servant uniquement aux anciennes constructions E1,
   sémantiques parallèles, progressions ou histoires de théories.
5. Porter ou réécrire les seuls modules retenus sous le répertoire d’instance.
6. Construire le vérificateur HA, sa correction, la diagonalisation interne et
   la représentation du prédicat de preuve.
7. Instancier l’interface générique.
8. Appliquer le théorème générique sans redéfinir la présentation ni la preuve
   terminale.

### Gate de non-vacuité

La tâche de bout en bout n’est pas terminée tant que l’instance HA ne ferme pas
tous les champs sans recevoir la conclusion comme hypothèse. Si cette
réalisation exige réellement de nombreux auxiliaires, leur nombre est accepté
uniquement comme coût démontré de l’instance, jamais comme extension du cadre
générique.

`Tests/HeytingArithmeticGodelInstanceRegression.lean` contrôle le nom de
l’instance, le vérificateur exact, le point fixe produit et l’application du
théorème générique.

## Phase 12 — intégration publique et documentation scientifique

Seulement après les phases Lean et les tests :

- importer le théorème générique et l’unique instance dans la surface publique
  appropriée ;
- ajouter les modules à `scripts/stratification.tsv` avec des responsabilités
  distinctes pour le cadre générique et l’instance ;
- intégrer seulement les fixtures réellement conservées dans
  `scripts/expected-failures.tsv` ;
- ajouter les tests aux agrégateurs existants ;
- déplacer le document cible unique vers
  `docs/godel-false-temoin-interne.fr.md`, conserver inchangés ses critères de
  portée, mettre à jour son statut factuel après vérification et y ajouter une
  unique section `Conclusion canonique à portée explicite` ;
- créer une seule entrée `GODEL_*` dans `docs/scientific-claims.json` ;
- ancrer une conclusion canonique unique ;
- enregistrer les preuves génériques, l’instance et les tests avec leurs rôles
  exacts ;
- remplir séparément formation, exécution, preuve et transport ;
- laisser les revues à `pending` et l’audit indépendant à `not_recorded` tant
  qu’aucun rapport valide n’a été lu et enregistré.

Le présent plan est temporaire et doit être retiré avant intégration dans
`main`, conformément à la procédure scientifique.

### Séquence des révisions d’évidence

Le registre ne peut pas inventer une révision future. L’ordre est donc :

1. terminer les sources, tests et le document canonique, puis exécuter les
   contrôles préalables sans créer d’évidence ;
2. demander l’autorisation humaine de créer le commit de référence ;
3. après ce commit, enregistrer son SHA et ses empreintes dans le registre ;
4. demander séparément l’autorisation de commiter cette mise à jour du
   registre ;
5. vérifier l’arbre suivi propre et toutes les gates sur le commit résultant.

Un audit extérieur éventuel doit viser le SHA final exact, distinctement de la
révision d’évidence interne, et requiert une autorisation explicite.

## Phase 13 — vérification complète

### Contrôles locaux pendant l’implémentation

Pour chaque fichier Lean créé ou modifié :

- compilation isolée avec la toolchain épinglée ;
- recherche des mécanismes interdits ;
- exactement un bloc `AXIOM_AUDIT` final ;
- lecture des énoncés complets et des corps des cinq fonctions causales
  centrales ;
- vérification du diff avant de passer à la phase suivante.

### Gates finales obligatoires

Depuis un arbre suivi propre :

```text
python3 scripts/check-scientific-docs.py --self-test
python3 scripts/check-scientific-docs.py --static
lake build
python3 scripts/check-scientific-docs.py --lean
bash scripts/verify.sh
pwsh -NoProfile -File scripts/verify.ps1
```

Contrôles supplémentaires :

- `git diff --check` ;
- comparaison exhaustive avec `origin/main` ;
- vérification qu’aucun fichier hors périmètre n’a été ajouté ;
- vérification des liens locaux et de l’unique passage canonique ;
- confirmation que `StrongPerimetralTurning.lean` reste identique à `main` ;
- confirmation qu’aucun ancien plan, prompt d’audit ou résultat brut n’est
  suivi ;
- audit sans axiome des déclarations publiques et de l’instance HA ;
- nouvelle exécution des gates sur le commit de référence propre, uniquement
  après autorisation de commit.

Aucun push, aucune fusion et aucun audit extérieur ne sont inclus dans cette
phase sans demande humaine explicite.

## Matrice de traçabilité des quatorze critères

| Critère de la cible | Phase qui le ferme | Évidence formelle attendue |
| --- | ---: | --- |
| 1. Production avant inscription | 2–3 | production portée par le témoin puis utilisée pour construire `P` |
| 2. Continuation consommant la production | 3–4 | ressources typées, occurrences exactes et `H` indexée par `P witness` |
| 3. Admission fondationnelle exacte | 5 | sigma dépendant raffinement/témoin positif |
| 4. Tentative contenant les totalisations réelles | 5–6 | application de `realizesFinal`, projections directes |
| 5. Aucun accès à l’obstruction | 6–8 | corps complets des fonctions et graphe d’appels |
| 6. Contraction vers complétude | 7 | noyau positif, contraction, `Eq.mp` |
| 7. Même `G` partout | 2–3 | types dépendants et égalités de production |
| 8. Provenance contre le témoin étranger | 3–4, 10 | provenance `candidate = witness` et échec attendu ciblé |
| 9. `Truth → Proof → Empty → False` | 7–8 | deux déclarations terminales séparées |
| 10. Témoins affirmatifs conservés | 4, 9 | paquet final positif |
| 11. Rejet initial construit depuis `G` | 3 | corps de `godelCircularPresentation` |
| 12. Générique distinct de HA | 1–9, 11 | séparation des modules et application de l’instance |
| 13. Quatre lectures séparées | 9, 12 | champs du paquet et entrée de registre |
| 14. Texte exactement borné | 12–13 | passage canonique, relecture autonome et gates documentaires |

## Conditions d’arrêt

L’implémentation doit s’arrêter et signaler le blocage si :

- la cible exige en réalité une modification de la fondation ;
- la conversion `Truth(G) → Proof(G)` ne peut être construite sans projeter une
  obstruction ou utiliser une contradiction préalable ;
- l’identité du témoin ne peut être conservée sans reconstruction indépendante ;
- l’instance HA ne ferme pas constructivement un champ requis ;
- une gate impose d’affaiblir le contrat, de modifier la quantification ou de
  réintroduire une ancienne cible.

Dans aucun de ces cas le plan n’autorise une définition de remplacement.

## Définition de « terminé »

Le lot est terminé uniquement lorsque :

1. le théorème générique expose toute la chaîne causale exigée ;
2. la preuve canonique utilise une totalisation fondationnelle et son noyau
   positif sans accès à l’obstruction ;
3. le même témoin diagonal est produit, certifié, inscrit, continué et consommé ;
4. `Empty`, puis `False`, proviennent de la complétude produite et de la
   non-prouvabilité de ce témoin ;
5. le tout et la continuation positive restent disponibles ;
6. l’unique instance HA ferme les prémisses génériques ;
7. tous les tests, audits d’axiomes, gates documentaires et builds réussissent ;
8. le diff final ne contient aucun ajout hors cible ;
9. les limites et statuts de revue sont rapportés sans promettre un verdict
   extérieur.
