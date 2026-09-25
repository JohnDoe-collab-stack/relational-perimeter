# Cible de travail — stabilité opérationnelle endogène et branchement exponentiel

> **Statut : document de chantier.** Ce fichier fixe la cible scientifique et
> technique de la branche `codex/operational-stability-target`. Il devra être
> supprimé avant la fusion dans `main`, conformément aux règles du dépôt.

## 1. Résultat visé

Le résultat public doit rendre explicite la chaîne suivante :

```text
constitution relationnelle des objets
→ ouverture structurelle
→ reconstruction endogène d'un transport
→ stabilité démontrée du critère
→ détermination des obligations indépendantes
→ largeur opérationnelle uniformément bornée
→ absence d'accumulation exponentielle des obligations
→ non-factorisation de l'existence du témoin par l'état projeté
→ non-factorisation du profil de stabilisation par l'état projeté
→ transmission du résultat au stade suivant
```

La formulation conceptuelle canonique est :

> **The framework first constitutes the structured objects on which the
> computation acts. The computation then constitutes their operational status
> by determining whether structurally distinct alternatives must be carried as
> independent obligations. Stability under the reconstructed transformations
> prevents structural multiplicity from becoming exponential operational
> width.**

Le résultat formel correspondant doit porter sur l'exécution causale faisant
autorité, et non sur une trajectoire parallèle construite uniquement pour les
besoins de la preuve.

## 2. Force exacte de la revendication

Le dépôt doit établir simultanément les points suivants.

1. L'ouverture produit deux alternatives structurellement distinctes.
2. Leur indépendance opérationnelle ne découle pas de cette seule distinction.
3. Une relation entre les alternatives est reconstruite par l'exécution.
4. Cette reconstruction effectue une recherche réelle et rencontre des
   candidats qui échouent.
5. Le transport découvert agit sur des continuations arbitraires, sans recevoir
   de preuve d'acceptation comme entrée.
6. La préservation de l'acceptation et de la viabilité est démontrée séparément.
7. Cette préservation autorise l'absorption d'une obligation sans identifier les
   alternatives et sans prouver l'impossibilité de l'alternative absorbée.
8. Chaque étape exécutée porte son propre témoin de stabilité, issu de la
   découverte réellement produite à cette étape.
9. La frontière opérationnelle suit le profil `1 → 2 → 1` à chaque étape.
10. Sur une histoire de `n` étapes, la trace de largeur contient exactement
    `2 * n + 1` entrées.
11. Toute largeur enregistrée vaut `1` ou `2`, donc elle est uniformément bornée
    par `2`, indépendamment de la profondeur.
12. La stabilité et la borne de largeur sont intégrées au même paquet d'évidence
    que l'histoire causale, la provenance, la décision et la comptabilité.
13. L'état retenu, la graine et la provenance produits conditionnent la
    reconstruction suivante.
14. Cette stabilité de la décomposition opérationnelle est distinguée des
    notions classiques qui étudient une dynamique déjà constituée.
15. Deux constitutions ayant la même projection d'état diffèrent quant à
    l'existence d'un type habité portant l'étape stabilisatrice complète.
16. Le profil `some [1, 2, 1]` contre `none` ne se factorise pas davantage par
    cette projection.

La conséquence publique doit être lisible directement :

```text
stabilité reconstruite à chaque étape
+ succession depuis le singleton retenu
⇒ largeur opérationnelle bornée indépendamment de la profondeur
```

## 3. Distinctions à préserver

L'implémentation doit maintenir dans les types les séparations suivantes :

```text
multiplicité structurelle       ≠ indépendance opérationnelle
ouverture de deux alternatives  ≠ conservation de deux obligations
transport de continuations      ≠ préservation de l'acceptation
préservation d'un critère       ≠ égalité des alternatives
absorption d'une obligation     ≠ impossibilité de l'alternative
largeur opérationnelle          ≠ coût total de l'exécution
borne uniforme de largeur       ≠ solveur polynomial universel
stabilité locale par étape      ≠ équivalence globale entre systèmes distincts
stabilité opérationnelle endogène ≠ stabilité classique d'une dynamique donnée
état projeté                    ≠ disponibilité d'une stabilisation construite
résultat de découverte          ≠ témoin exécuté de stabilisation
```

La stabilité pertinente est **locale et certifiée à chaque étape**. Les racines
et les systèmes typés peuvent changer au cours de l'exécution ; il ne faut donc
pas fabriquer une composition globale de préservations dont les domaines ne
coïncident pas.

## 4. Évidence déjà présente

La nouvelle implémentation doit réemployer les constructions existantes.

### Ouverture, transport et préservation

- `EndogenousFlipDiscovery.fullStepPreservation` compose l'ouverture du parent
  et l'absorption du premier enfant dans le second.
- `applyFullConstitutiveStep` agit sur une continuation arbitraire.
- `applyFullConstitutiveStep_preservesAccept` démontre séparément la
  préservation de l'acceptation.
- `ThreadedConstitutiveStageRun` relie la découverte, le code retourné,
  l'application exécutée et l'état suivant.

### Histoire causale

- `ConstitutiveExecutionHistory` est produite récursivement depuis l'état
  courant.
- Chaque constructeur `step` contient le `ThreadedConstitutiveStageRun` de sa
  tête et une queue indexée par l'état effectivement produit.
- L'échec de la découverte ne produit ni étape construite ni histoire
  descendante positive.
- `ThreadedConstitutiveRoleStage` rassemble déjà, pour une étape de cette même
  histoire, l'ouverture structurelle, la décision exécutée, la provenance de la
  relation reconstruite, la continuation produite et l'état suivant.
- `ThreadedConstitutiveRoleHistory` suit récursivement la queue dépendante de
  `ConstitutiveExecutionHistory`. Cette structure existante doit devenir le
  support de la stabilité ; il ne faut pas construire une seconde histoire de
  témoins en parallèle.

### Largeur et stabilité dans la famille symétrique antérieure

- `FlipSymmetricTrajectory.viable_iff` donne l'équivalence de viabilité.
- `FlipSymmetricTrajectory.widthTrace_length` donne `2 * n + 1`.
- `FlipSymmetricTrajectory.widthTrace_value` classe chaque largeur en `1` ou
  `2`.
- `FlipSymmetricTrajectory.width_le_two` donne la borne uniforme.
- `ExplicitFamilyCertifiedCounts` rassemble déjà les comptes structurels de la
  famille explicite.

Ces résultats antérieurs servent de référence et de régression. Ils ne doivent
pas être présentés comme s'ils portaient déjà, par définition, sur l'histoire
causale intégrée actuelle.

## 5. Lacune exacte à fermer

Le module public expose actuellement :

- la distinction structurelle des alternatives ;
- la transformation des continuations ;
- la préservation séparée ;
- l'absorption préservant la viabilité ;
- la recherche et ses échecs ;
- la transmission de la graine et de la provenance ;
- la non-factorisation de la découverte suivante.

Il n'expose pas encore un certificat unique, construit depuis
`run.constitutiveFeedbackHistory`, qui associe à cette même histoire :

- les témoins de stabilité de toutes ses étapes ;
- sa trace opérationnelle de largeur ;
- la forme alternée exacte de cette trace ;
- la longueur exacte de cette trace ;
- la borne uniforme `≤ 2` ;
- le raccord entre la largeur de la frontière retenue et la largeur initiale de
  la situation suivante.

Il n'expose pas non plus le séparateur causal plus fort qui montre, pour deux
constitutions issues d'une origine exécutée commune et ayant la même projection
d'état :

- que la constitution retenue habite le type complet de stabilisation ;
- que la constitution bloquée ne peut habiter ce type ;
- que leurs profils calculables valent respectivement `some [1, 2, 1]` et
  `none` ;
- que ni l'habitabilité du témoin ni le profil ne se factorisent par la
  projection.

La cible de la branche est de fermer cette lacune sans réécrire la computation
et sans introduire une seconde exécution.

## 6. Topologie de dépendances visée

Créer les modules canoniques :

```text
RelationalPerimeter/Computation/ConstitutiveSearch/
  EndogenousDecomposition/OperationalStability.lean
RelationalPerimeter/Computation/ConstitutiveSearch/
  EndogenousDecomposition/ProjectedStabilizationBoundary.lean
```

La dépendance doit devenir :

```text
ConstitutiveFullStep
→ ConstitutiveFeedback
→ OperationalStability
→ ProjectedStabilizationBoundary
→ ConstitutiveResolution
→ MeasuredAccounting
→ EndogenousOperationalDecomposition
→ RelationalPerimeter
```

`OperationalStability.lean` doit importer l'histoire causale existante.
`ProjectedStabilizationBoundary.lean` doit importer le certificat de stabilité
et la non-factorisation constructive déjà disponible. Aucun des deux modules ne
doit reconstruire la recherche, dupliquer les étapes ou créer une nouvelle
famille SAT.

## 7. API interne proposée

Les signatures ci-dessous fixent le contrat conceptuel. Les univers et les
arguments implicites pourront être ajustés lors de l'élaboration Lean sans en
modifier la substance.

### 7.1 Compléter le rôle d'une étape exécutée

```lean
structure ThreadedConstitutiveRoleStage
    (run : ThreadedConstitutiveStageRun state stage) where
  -- champs existants : état, ouverture, décision, relation, exécution, suivant
  ...
  operationalAbsorption :
    AcceptedFrontierPreservation
      (generatedStructuralBranchSystem ...)
      [leftChild, rightChild]
      [retained]
```

Le constructeur canonique doit remplir ce champ par :

```lean
AcceptedFrontierPreservation.absorbFirstIntoSecond
  stage.discovery.relation.toAcceptingTransport
```

La découverte `stage.discovery` est déjà reliée au résultat de recherche de
l'état transmis par `reconstructedRelationComesFromTransmittedState`. Le témoin
de préservation est ainsi attaché à la même relation que l'exécution, et non à
une relation extérieure.

L'ouverture et la préservation complète se déduisent sans nouvelle donnée :

```lean
def ThreadedConstitutiveRoleStage.openingPreservation ... :=
  AcceptedFrontierPreservation.expandHead roles.structuralOpening

def ThreadedConstitutiveRoleStage.fullOperationalPreservation ... :=
  roles.openingPreservation.trans roles.operationalAbsorption
```

Les trois frontières doivent apparaître dans les types :

```text
[parent] ↔ [leftChild, rightChild] ↔ [retained]
```

Le premier raccord vient de l'ouverture exacte ; le second utilise la relation
reconstruite. C'est ce second témoin qui établit que la multiplicité ouverte ne
doit pas être conservée comme deux obligations indépendantes pour le critère.

Exposer ensuite les deux invariances :

```lean
theorem ThreadedConstitutiveRoleStage.opened_retained_viable_iff
    (roles : ThreadedConstitutiveRoleStage run) :
    FrontierViable system [leftChild, rightChild] ↔
      FrontierViable system [retained] :=
  roles.operationalAbsorption.viable_iff

theorem ThreadedConstitutiveRoleStage.source_retained_viable_iff
    (roles : ThreadedConstitutiveRoleStage run) :
    FrontierViable system [parent] ↔
      FrontierViable system [retained] :=
  roles.fullOperationalPreservation.viable_iff
```

Le type du témoin d'absorption doit mentionner les enfants de la découverte
portée par l'étape ; une relation extérieure ne doit pas pouvoir être
substituée. `stage.discovery.fullStepPreservation` reste une régression utile,
mais ne doit pas remplacer dans l'API le raccord intermédiaire explicite
`2 → 1`.

### 7.2 Utiliser l'histoire de rôles déjà dépendante

`ThreadedConstitutiveRoleHistory` est déjà une famille dans `Type` indexée par
l'histoire causale exacte. Après l'ajout du champ précédent, chaque constructeur
`step` contiendra automatiquement :

- l'ouverture binaire exacte ;
- la relation issue de la recherche de l'état transmis ;
- le témoin d'absorption préservant la viabilité de la frontière ouverte vers
  la cible retenue ;
- la continuation exécutée ;
- l'état suivant ;
- la queue construite depuis cet état suivant.

Il ne faut donc pas ajouter une nouvelle
`OperationalStabilityEvidence` récursive à côté de
`ThreadedConstitutiveRoleHistory`. La stabilité doit enrichir la chaîne de rôles
existante et rester accessible dans chaque tête.

### 7.3 Frontières et largeurs d'une étape

Définir depuis les indices de `ThreadedConstitutiveRoleStage` les trois
frontières effectivement concernées :

```lean
def ThreadedConstitutiveRoleStage.sourceFrontier := [parent]
def ThreadedConstitutiveRoleStage.openedFrontier := [leftChild, rightChild]
def ThreadedConstitutiveRoleStage.retainedFrontier := [rightChild]
```

Puis démontrer par réduction :

```lean
theorem sourceFrontier_length : roles.sourceFrontier.length = 1
theorem openedFrontier_length : roles.openedFrontier.length = 2
theorem retainedFrontier_length : roles.retainedFrontier.length = 1
```

Les valeurs `1` et `2` ne doivent donc pas être de simples annotations. Elles
doivent être les longueurs des listes de frontières typées par l'ouverture et
la préservation de l'étape réelle. En particulier, `openedFrontier` doit être
exactement la source de `operationalAbsorption`, et `retainedFrontier` sa cible.

Il faut également réutiliser les raccords existants pour rendre explicite que :

- la cible retenue est celle de `operationalAbsorption` et de
  `fullOperationalPreservation` ;
- `completeExecution.output` habite cette cible ;
- `outputBecomesNextCondition` identifie son affectation à celle de l'état
  suivant ;
- la queue de l'histoire recommence depuis cet état suivant unique.

Les objets de deux stades successifs n'habitent pas nécessairement le même
système de recherche. Le raccord exigé n'est donc pas une égalité artificielle
entre leurs carriers : c'est la transmission dépendamment typée de la sortie
exécutée vers l'état suivant, accompagnée de l'égalité quantitative entre la
largeur retenue et la largeur initiale suivante.

### 7.4 Trace certifiée unique

La trace doit être dérivée de `ThreadedConstitutiveRoleHistory`, qui porte déjà
les témoins, et non recalculée indépendamment depuis un simple compteur. Le cas
terminal doit lui aussi lire la longueur d'un singleton construit depuis l'état
terminal, plutôt qu'insérer une constante sans carrier :

```lean
def singletonFrontierWidth (state : α) : Nat := [state].length

def ThreadedConstitutiveRoleHistory.operationalWidthTrace :
    ThreadedConstitutiveRoleHistory history → List Nat
  | .nil (state := state) => [singletonFrontierWidth state]
  | .step headRole tailRoles =>
      headRole.sourceFrontier.length ::
        headRole.openedFrontier.length ::
          tailRoles.operationalWidthTrace

def alternatingOperationalWidthTrace : Nat → List Nat
  | 0 => [1]
  | count + 1 => 1 :: 2 :: alternatingOperationalWidthTrace count
```

Établir constructivement :

```lean
theorem ThreadedConstitutiveRoleHistory.operationalWidthTrace_exact :
    roles.operationalWidthTrace = alternatingOperationalWidthTrace count

theorem ThreadedConstitutiveRoleHistory.operationalWidthTrace_length :
    roles.operationalWidthTrace.length = 2 * count + 1

theorem ThreadedConstitutiveRoleHistory.operationalWidthTrace_value
    (member : width ∈ roles.operationalWidthTrace) :
    width = 1 ∨ width = 2

theorem ThreadedConstitutiveRoleHistory.operationalWidth_le_two
    (member : width ∈ roles.operationalWidthTrace) :
    width ≤ 2
```

Pour une tête et sa queue, ajouter un théorème de raccord quantitatif :

```lean
theorem retainedWidth_eq_nextInitialWidth
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun) :
    headRole.retainedFrontier.length = tailRoles.initialOperationalWidth
```

Ce théorème ne confond pas les carriers successifs. Il affirme exactement que
l'unique obligation retenue devient l'unique condition initiale de la situation
suivante, tandis que la dépendance de `tailRun` envers `headRun.nextRun.next`
conserve le raccord constitutif.

### 7.5 Certificat intégré

```lean
structure OperationalStabilityCertificate
    (history : ConstitutiveExecutionHistory (count := count) state)
    (roles : ThreadedConstitutiveRoleHistory history) :
    Type 2 where
  widthTraceLength :
    roles.operationalWidthTrace.length = 2 * count + 1
  widthTraceExact :
    roles.operationalWidthTrace = alternatingOperationalWidthTrace count
  widthValuesAreOneOrTwo :
    ∀ width, width ∈ roles.operationalWidthTrace → width = 1 ∨ width = 2
  widthUniformlyBounded :
    ∀ width,
      width ∈ roles.operationalWidthTrace →
        width ≤ 2

def ThreadedConstitutiveRoleHistory.operationalStabilityCertificate
    (roles : ThreadedConstitutiveRoleHistory history) :
    OperationalStabilityCertificate history roles
```

L'indice `roles` porte déjà tous les témoins de stabilité. Un seul objet récursif
— `ThreadedConstitutiveRoleHistory` — doit ainsi fournir à la fois les témoins
et la trace de largeur. Aucune seconde histoire et aucune seconde exécution ne
doivent être introduites ; les projections et preuves peuvent parcourir
structurellement l'unique chaîne de rôles déjà produite.

### 7.6 Non-factorisation de la stabilisation construite

La limite d'une analyse d'état fixée ne doit pas être illustrée par deux
présentations choisies arbitrairement. Elle doit porter sur l'habitabilité d'un
type construit par l'exécution : les données d'état projetées déterminent-elles
si une étape stabilisatrice complète peut exister ?

Définir le type positif du témoin :

```lean
structure OperationalStabilizationWitness
    (constitution : NextDiscoveryConstitution depth) : Type 2 where
  history :
    ConstitutiveExecutionHistory
      (count := 1)
      constitution.packed.state
  roles : ThreadedConstitutiveRoleHistory history
  stability : OperationalStabilityCertificate history roles

def OperationalStabilizationAvailable
    (constitution : NextDiscoveryConstitution depth) : Prop :=
  Nonempty (OperationalStabilizationWitness constitution)
```

Le témoin retenu doit être construit par
`executeConstitutiveExecutionHistory 1` sur
`retainedNextDiscoveryState depth`, avec
`retainedNextDiscoveryState_fresh depth`, puis enrichi par
`buildThreadedConstitutiveRoleHistory`, puis certifié par
`roles.operationalStabilityCertificate`. Il ne doit pas être postulé depuis le
seul fait que `nextDiscoveryOutcome` vaut `some`. Son champ `history` contient
le stage exécuté et l'état suivant ; son champ `roles` contient l'ouverture, la
relation reconstruite et le témoin d'absorption ; son champ `stability` établit
la trace exacte et sa borne.

Pour l'état bloqué, démontrer la négation à partir de
`nextDiscovery_blocked_none` et `failedDiscovery_noPositiveHistory`. Les deux
constitutions doivent rester celles du séparateur existant, issu d'une origine
exécutée commune : l'organisation retenue est produite par l'exécution ;
l'organisation bloquée est construite contrefactuellement depuis cette origine
pour éprouver la suffisance de la projection.

Démontrer ensuite :

```lean
theorem retained_operationalStabilizationAvailable (depth : Nat) :
  OperationalStabilizationAvailable
    (nextDiscoveryConstitution depth .retained)

theorem blocked_operationalStabilizationUnavailable (depth : Nat) :
  ¬ OperationalStabilizationAvailable
    (nextDiscoveryConstitution depth .blocked)

theorem operationalStabilizationAvailability_not_factors
    (depth : Nat) :
  ¬ PredicateFactorsThrough
      (nextDiscoveryProjection (depth := depth))
      (OperationalStabilizationAvailable (depth := depth))

theorem operationalStabilizationAvailability_not_factors_through_view
    (depth : Nat) {View : Type}
    (view :
      (SequentialAssignment (depth + 1) ×
        CanonicalStageGeneration (depth + 1) × Nat) → View) :
  ¬ PredicateFactorsThrough
      (fun constitution => view (nextDiscoveryProjection constitution))
      (OperationalStabilizationAvailable (depth := depth))
```

Cette preuve doit employer `predicate_not_factors_of_same_projection` avec
`nextDiscovery_projection_equal`. Elle renforce
`nextDiscovery_not_factors` : la projection ne perd pas seulement la valeur du
résultat de découverte ; elle perd la possibilité même de construire le type
qui porte l'ouverture, la relation reconstruite, la préservation et l'état
suivant.

Un prototype Lean temporaire, supprimé après vérification, valide cette
architecture en conservant le témoin comme une structure dans `Type 2`.
L'extraction préalable d'un stage par réduction de l'histoire est inutilement
coûteuse ; la construction directe de l'histoire de longueur `1`, suivie de sa
chaîne de rôles et de son certificat, compile sans axiome et garde davantage de
dépendances visibles dans le type.

Définir également une observation calculable de la décomposition. Le profil
d'une découverte doit être calculé depuis les longueurs de ses trois frontières
typées :

```lean
def discoveryWidthProfile
    {root : Cnf} {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state) : List Nat :=
  let source := [state]
  let opened :=
    [state.child discovery.var false discovery.fresh,
      state.child discovery.var true discovery.fresh]
  let retained := [state.child discovery.var true discovery.fresh]
  [source.length, opened.length, retained.length]

def operationalStabilizationProfile
    (constitution : NextDiscoveryConstitution depth) : Option (List Nat) :=
  (nextDiscoveryOutcome constitution).map discoveryWidthProfile
```

Le profil numérique doit se réduire à
`some [1, 2, 1]` pour la constitution retenue et à `none` pour la constitution
bloquée ; il ne doit pas être une constante décorative.

Démontrer :

```lean
theorem retained_operationalStabilizationProfile (depth : Nat) :
  operationalStabilizationProfile
    (nextDiscoveryConstitution depth .retained) = some [1, 2, 1]

theorem blocked_operationalStabilizationProfile (depth : Nat) :
  operationalStabilizationProfile
    (nextDiscoveryConstitution depth .blocked) = none

theorem operationalStabilizationProfile_not_factors (depth : Nat) :
  ¬ ValueFactorsThrough
      (nextDiscoveryProjection (depth := depth))
      (operationalStabilizationProfile (depth := depth))

theorem operationalStabilizationProfile_not_factors_through_view
    (depth : Nat) {View : Type}
    (view :
      (SequentialAssignment (depth + 1) ×
        CanonicalStageGeneration (depth + 1) × Nat) → View) :
  ¬ ValueFactorsThrough
      (fun constitution => view (nextDiscoveryProjection constitution))
      (operationalStabilizationProfile (depth := depth))
```

La non-factorisation du profil complète celle de l'habitabilité : la même
projection ne détermine ni l'existence du témoin dépendant ni le profil de
largeur effectivement disponible. Les deux variantes `through_view` rendent
explicite que toute vue calculée uniquement depuis cette projection perd au
moins autant d'information ; elles se prouvent avec le même séparateur et
`congrArg view nextDiscovery_projection_equal`.

Le certificat final doit réunir ces résultats :

```lean
structure ProjectedStabilizationBoundaryCertificate (depth : Nat) : Type 2 where
  retainedWitness :
    OperationalStabilizationWitness
      (nextDiscoveryConstitution depth .retained)
  blockedUnavailable :
    ¬ OperationalStabilizationAvailable
      (nextDiscoveryConstitution depth .blocked)
  sharedProjectedState :
    nextDiscoveryProjection (nextDiscoveryConstitution depth .retained) =
      nextDiscoveryProjection (nextDiscoveryConstitution depth .blocked)
  retainedProfileExact :
    operationalStabilizationProfile
      (nextDiscoveryConstitution depth .retained) = some [1, 2, 1]
  blockedProfileExact :
    operationalStabilizationProfile
      (nextDiscoveryConstitution depth .blocked) = none
  stabilizationAvailabilityNotProjected :
    ¬ PredicateFactorsThrough
        (nextDiscoveryProjection (depth := depth))
        (OperationalStabilizationAvailable (depth := depth))
  stabilizationProfileNotProjected :
    ¬ ValueFactorsThrough
        (nextDiscoveryProjection (depth := depth))
        (operationalStabilizationProfile (depth := depth))
```

Ce certificat appartient à `ProjectedStabilizationBoundary.lean`, qui importe
`OperationalStability.lean`. Cette séparation évite toute dépendance circulaire
entre le certificat de largeur de l'histoire faisant autorité et le séparateur
causal utilisé pour éprouver la projection. Le certificat ne doit jamais faire
passer l'état bloqué contrefactuel pour un état émis par l'exécution principale.

## 8. Intégration dans l'évidence finale

Ajouter à `EndogenousOperationalDecompositionEvidence` deux champs clairement
séparés : le premier dépend de l'histoire exécutée faisant autorité ; le second
dépend du séparateur causal construit pour le même `input` :

```lean
operationalStability :
  OperationalStabilityCertificate
    run.constitutiveFeedbackHistory
    feedbackRolesFollowThreadedHistory

projectedStabilizationBoundary :
  ProjectedStabilizationBoundaryCertificate input
```

Le champ `operationalStability` doit être placé après
`feedbackRolesFollowThreadedHistory`, puisqu'il en dépend dans son type. Le champ
`projectedStabilizationBoundary` reste indépendant du run public et doit être
placé avec les résultats de non-factorisation. Dans
`ConstitutiveResolution.lean`, l'import direct de `ConstitutiveFeedback` doit
être remplacé par `ProjectedStabilizationBoundary` afin que la topologie
annoncée soit la topologie effective.

Leurs valeurs doivent être :

```lean
feedbackRolesFollowThreadedHistory.operationalStabilityCertificate
projectedStabilizationBoundaryCertificate input
```

Les deux certificats deviennent ainsi des composantes de `core`, puis de
`EndogenousOperationalDecompositionPerInputEvidence`, sans duplication dans le
ledger de comptabilité. La documentation et les noms de champs ne doivent
jamais présenter le run séparateur comme la source de la trace de largeur
publique.

`EndogenousOperationalDecompositionFamily` doit continuer à fournir :

- la famille fermée pour toute entrée ;
- les croissances strictes mesurées ;
- les bornes polynomiales du travail instrumenté ;
- les non-factorisations.

La stabilité et la largeur viennent de l'évidence causale par entrée ; la borne
de travail reste une propriété distincte de la famille mesurée.

## 9. API publique proposée

Dans
`RelationalPerimeter/Computation/EndogenousOperationalDecomposition.lean`,
exposer :

```lean
abbrev EndogenousOperationalStabilityEvidence
    (input : Nat) : Type _ :=
  OperationalStabilityCertificate
    (evidence input).core.run.constitutiveFeedbackHistory
    (evidence input).core.feedbackRolesFollowThreadedHistory

def endogenousOperationalStability
    (input : Nat) :
    EndogenousOperationalStabilityEvidence input :=
  (evidence input).core.operationalStability

abbrev ProjectedStabilizationBoundaryEvidence
    (input : Nat) : Type _ :=
  ProjectedStabilizationBoundaryCertificate input

def projectedStabilizationBoundary
    (input : Nat) :
    ProjectedStabilizationBoundaryEvidence input :=
  (evidence input).core.projectedStabilizationBoundary
```

Et les projections publiques :

```lean
theorem operational_width_trace_exact (input : Nat) :
  ... = alternatingOperationalWidthTrace (input + 1)

theorem operational_width_trace_length_exact (input : Nat) :
  ... = 2 * (input + 1) + 1

theorem operational_width_uniformly_bounded
    (input width : Nat)
    (member : width ∈ ...) :
  width ≤ 2

theorem projected_state_cannot_determine_stabilization_availability
    (input : Nat) :
  (projectedStabilizationBoundary input).stabilizationAvailabilityNotProjected

theorem projected_state_cannot_determine_stabilization_profile
    (input : Nat) :
  (projectedStabilizationBoundary input).stabilizationProfileNotProjected

theorem projected_view_cannot_determine_stabilization_availability
    (input : Nat) (view : ... → View) :
  ¬ PredicateFactorsThrough
      (fun constitution => view (nextDiscoveryProjection constitution))
      (OperationalStabilizationAvailable (depth := input))

theorem projected_view_cannot_determine_stabilization_profile
    (input : Nat) (view : ... → View) :
  ¬ ValueFactorsThrough
      (fun constitution => view (nextDiscoveryProjection constitution))
      (operationalStabilizationProfile (depth := input))
```

Le nom public principal doit désigner le contenu constitutif du résultat : une
stabilité opérationnelle produite par l'exécution elle-même. La documentation
peut parler de stabilité contre le branchement exponentiel parce que le
certificat contient l'énoncé positif exact qui l'établit pour la largeur
opérationnelle : une borne `2` indépendante de la profondeur. Les théorèmes de
noyau doivent rester nommés d'après leur contenu mathématique exact.

## 10. Relation avec l'exponentielle

Le code de production ne doit pas inventer un arbre contrefactuel de taille
`2 ^ n` uniquement pour produire une comparaison spectaculaire.

L'énoncé formel pertinent est plus direct :

```text
∀ n, ∀ width ∈ operationalWidthTrace(n), width ≤ 2
```

Une borne indépendante de `n` exclut immédiatement toute croissance
exponentielle de cette largeur opérationnelle. La documentation peut expliquer
le contraste avec une accumulation binaire non réduite :

```text
ouverture non réduite : 1, 2, 4, 8, ..., 2^n
exécution certifiée    : 1, 2, 1, 2, ..., 1
```

Cette comparaison est explicative. Le théorème Lean porte sur la trace réelle.

## 11. Stabilité opérationnelle endogène et stabilité classique

Le résultat doit être présenté explicitement comme une **stabilité
opérationnelle endogène**.

À chaque étape réellement exécutée :

1. l'ouverture constitue deux alternatives structurellement distinctes ;
2. la découverte exécutée reconstruit une transformation sur des continuations
   arbitraires ;
3. le témoin séparé de préservation établit que le critère retenu est stable
   sous cette transformation ;
4. l'histoire causale conserve une seule obligation opérationnelle pour l'étape
   suivante ;
5. la même reconstruction recommence depuis l'état effectivement produit.

La stabilité ne signifie donc ni immobilité, ni égalité des alternatives, ni
impossibilité de l'alternative absorbée. Elle signifie que la transformation
reconstruite pendant l'exécution préserve le critère pertinent et empêche les
distinctions structurelles déjà traitées de s'accumuler comme obligations
opérationnelles indépendantes. Le certificat de largeur montre l'effet global
de cette stabilité locale sur toute l'histoire exécutée.

Cette notion porte sur une donnée que les formulations classiques de la
stabilité ne demandent pas : la constitution des obligations opérationnelles.
Elles fixent un espace d'états et une évolution, puis étudient la réponse des
trajectoires aux perturbations exprimables dans cet espace. Elles ne reçoivent
pas nécessairement, même implicitement, une décomposition des états en
obligations de recherche. Ici, le calcul produit cette décomposition et décide,
depuis son propre matériau, quelles alternatives doivent compter comme
obligations indépendantes.

### Différence exacte dans les types

La comparaison ne doit pas rester formulée comme une simple succession
conceptuelle. Selon la variante topologique ou métrique retenue, une signature
lyapunovienne standard reçoit schématiquement des données de la forme :

```lean
State : Type u
Time : Type v
evolve : Time → State → State
equilibrium : State
nearness : State → State → Prop
-- éventuellement une fonction de Lyapunov : State → Value
```

Le jugement de stabilité quantifie alors sur des états proches et leur
évolution. Par ce seul typage, il ne comporte aucun indice disant comment une
étape a été ouverte en alternatives, comment son transport a été reconstruit,
ni lesquelles de ces alternatives doivent subsister comme obligations
indépendantes.

La construction présente possède au contraire les dépendances suivantes :

```lean
EndogenousFlipDiscovery (state : GeneratedStructuralBranchContext root) : Type

applyFullConstitutiveStep
  (discovery : EndogenousFlipDiscovery state) :
  GeneratedStructuralBranchContinuation state →
  GeneratedStructuralBranchContinuation
    (state.child discovery.var true discovery.fresh)

applyFullConstitutiveStep_preservesAccept
  (discovery : EndogenousFlipDiscovery state)
  (continuation : GeneratedStructuralBranchContinuation state) :
  GeneratedStructuralBranchAccept state continuation →
  GeneratedStructuralBranchAccept
    (state.child discovery.var true discovery.fresh)
    (applyFullConstitutiveStep discovery continuation)
```

`EndogenousFlipDiscovery state` est une somme dépendante. Son témoin contient
la variable effectivement trouvée, sa fraîcheur et une relation dont les types
indexent les deux enfants exacts de `state`. Le transport agit sur toute
continuation avant de recevoir une preuve d'acceptation ; la préservation est
un théorème séparé.

La dépendance se poursuit dans l'histoire :

```lean
ConstitutiveExecutionHistory (count := count) state : Type 2
```

Dans le constructeur `step`, la queue a précisément le type :

```lean
ConstitutiveExecutionHistory (count := count) headRun.nextRun.next
```

Elle ne peut donc pas être remplacée par une trajectoire partant d'un état
choisi indépendamment de la sortie exécutée. La cible ajoute enfin :

```lean
OperationalStabilityCertificate history roles : Type
```

où `roles : ThreadedConstitutiveRoleHistory history`. Le certificat de
stabilité est ainsi indexé simultanément par l'exécution qui a produit les
états et par la lecture des rôles construite sur cette même histoire.

La frontière formelle ne doit pas reposer sur un contraste entre deux
présentations choisies du même pas. Elle est établie par deux constitutions
raccordées à une origine exécutée commune :

```lean
nextDiscoveryConstitution depth .retained
nextDiscoveryConstitution depth .blocked
```

La première est l'état effectivement produit. La seconde est construite
contrefactuellement depuis le même target engendré, en ajoutant les décisions
qui bloquent la découverte suivante. Elles ont la même image par :

```lean
nextDiscoveryProjection :
  NextDiscoveryConstitution depth →
    SequentialAssignment (depth + 1) ×
      CanonicalStageGeneration (depth + 1) × Nat
```

Cette projection lit réellement l'affectation, la génération et la graine
transmise. Un troisième élément canonique du même domaine,
`nextDiscoveryConstitution depth .reference`, est distingué de l'état retenu
par cette projection : celle-ci est donc prouvée non constante. Elle omet
exactement l'histoire des décisions et la provenance qui distinguent les deux
constitutions du séparateur.

Le résultat positif puis négatif porte sur un type, et non sur une annotation :

```lean
OperationalStabilizationAvailable retained
¬ OperationalStabilizationAvailable blocked
operationalStabilizationProfile retained = some [1, 2, 1]
operationalStabilizationProfile blocked  = none
```

Il en résulte deux théorèmes constructifs. Ni le prédicat
`OperationalStabilizationAvailable`, ni la valeur calculable
`operationalStabilizationProfile`, ne se factorisent par
`nextDiscoveryProjection`. Une fonction de la seule valeur projetée doit rendre
le même résultat sur les deux constitutions ; les témoins construits imposent
des résultats différents.

C'est la frontière typée exacte avec une analyse d'état fixée : lorsque son
`State` est cette vue projetée, ni l'existence de l'étape stabilisatrice ni son
profil opérationnel ne sont des fonctions de l'état disponible. Une analyse de
Lyapunov enrichie pourrait les recevoir en ajoutant au type d'état l'histoire,
la provenance, la frontière et ses témoins. Cet enrichissement est possible,
mais il importe précisément la constitution opérationnelle absente de la
signature minimale. Le cadre localise donc le point d'augmentation nécessaire ;
il ne se contente pas d'affirmer verbalement un angle mort.

Le code et la documentation doivent toutefois maintenir une frontière nette :

- le résultat n'est pas un théorème de stabilité de Lyapunov ;
- il ne définit ni distance, ni perturbation métrique, ni convergence ;
- il ne prouve aucune équivalence avec une notion externe de stabilité
  numérique, logique, dynamique ou modèle-théorique ;
- il établit positivement, sur la famille construite, la préservation
  du critère étape par étape et la borne uniforme de la largeur
  opérationnelle.

La formulation publique visée est donc :

> **The framework first constitutes the structured objects on which the
> computation acts. The computation then endogenously stabilizes their
> operational decomposition by reconstructing criterion-preserving
> transformations that determine which structurally distinct alternatives
> must remain independent obligations.**

Cette formulation ne doit être publiée qu'avec les projections Lean qui
exhibent, sur la même exécution causale, le témoin de préservation de chaque
étape et la borne globale de largeur.

## 12. Tests de régression

Ajouter des protections dans `Tests/ConstitutiveExecutionRegression.lean` :

1. l'histoire vide a la trace `[1]` ;
2. une étape a la trace `[1, 2, 1]` ;
3. la trace générale est exactement `alternatingOperationalWidthTrace count` ;
4. sa longueur vaut `2 * count + 1` ;
5. chaque largeur générale est `1` ou `2` ;
6. chaque largeur de l'histoire publique est `≤ 2` ;
7. le certificat public est extrait de l'histoire causale du même `run` ;
8. le témoin d'absorption d'une étape utilise la découverte stockée dans
   cette étape et relie exactement la frontière ouverte à la frontière
   retenue ;
9. la largeur retenue d'une étape coïncide avec la largeur initiale de sa
   queue dépendante ;
10. la constitution retenue construit positivement un
    `OperationalStabilizationWitness` ;
11. ce témoin contient l'histoire d'une étape, sa chaîne de rôles et son
    certificat de stabilité ;
12. la constitution bloquée ne peut en construire aucun ;
13. les deux constitutions ont exactement la même
    `nextDiscoveryProjection` ;
14. un état canonique de référence du même domaine rend la projection
    constructivement non constante ;
15. leurs profils valent respectivement `some [1, 2, 1]` et `none` ;
16. la disponibilité du témoin ne se factorise pas par
    `nextDiscoveryProjection` ;
17. le profil de stabilisation ne se factorise pas davantage par cette
    projection ;
18. les deux non-factorisations persistent après toute nouvelle projection de
    ces données vers une vue plus pauvre ;
19. l'état bloqué est bien identifié comme un contrefactuel issu de l'origine
    exécutée commune, et non comme un état émis par le run public ;
20. l'ajout ne modifie ni les compteurs ni la comptabilité de l'exécution ;
21. les résultats publics antérieurs restent disponibles ;
22. aucune seconde exécution ne fournit le certificat de stabilité de
    l'histoire publique.

Étendre `Tests/PublicRootImport.lean` avec une définition consommant uniquement :

```lean
RelationalPerimeter.Computation.EndogenousOperationalDecomposition
  .endogenousOperationalStability

RelationalPerimeter.Computation.EndogenousOperationalDecomposition
  .projectedStabilizationBoundary
```

Cette gate doit démontrer que le résultat est réellement accessible depuis la
racine publique.

## 13. Documentation publique

Après compilation du certificat, ajouter une section bilingue :

- `Endogenous Operational Stability and Exponential Branching` ;
- `Stabilité opérationnelle endogène et branchement exponentiel`.

Elle doit expliquer :

- le passage `1 → 2 → 1` ;
- la stabilité de la viabilité ;
- la longueur exacte `2 * n + 1` ;
- la borne uniforme `W(n) ≤ 2` ;
- la séparation entre largeur et travail total ;
- le fait que l'alternative absorbée reste distincte et n'est pas déclarée
  impossible ;
- la position constitutive de cette stabilité en amont des analyses classiques
  de trajectoires déjà données ;
- la construction positive du témoin de stabilisation pour la constitution
  retenue et son impossibilité pour la constitution bloquée ;
- l'origine exécutée commune des deux constitutions et le statut explicitement
  contrefactuel de la constitution bloquée ;
- l'égalité de leur affectation, de leur génération et de leur graine dans
  `nextDiscoveryProjection` ;
- les deux théorèmes de non-factorisation qui portent respectivement sur
  l'habitabilité du témoin et sur le profil calculable `some [1, 2, 1]` contre
  `none` ;
- leur persistance pour toute vue ultérieure calculée uniquement depuis
  `nextDiscoveryProjection` ;
- l'absence de revendication concernant Lyapunov, une métrique, la convergence
  ou une théorie externe de la stabilité.

Mettre à jour :

- `README.md` ;
- `docs/endogenous-operational-decomposition.en.md` ;
- `docs/decomposition-operationnelle-endogene.fr.md` ;
- le SVG computationnel
  `docs/figures/endogenous-operational-decomposition.svg` si une représentation
  visuelle du profil `1 → 2 → 1` améliore effectivement la lecture.

Le SVG fondateur `relational-perimeter-formal-architecture.svg` ne doit pas être
modifié pour cette extension computationnelle.

## 14. Hors cible

Cette branche ne doit pas :

- modifier les quatre fichiers fondateurs ;
- définir une nouvelle sémantique de SAT ;
- créer une seconde famille destinée uniquement à illustrer la largeur ;
- remplacer l'histoire causale par `FlipSymmetricTrajectory` ;
- affirmer un résultat sur tous les espaces de recherche ;
- affirmer `P = NP` ou `P ≠ NP` ;
- déduire une borne de temps générale de la seule borne de largeur ;
- identifier la stabilité opérationnelle endogène à une stabilité de Lyapunov,
  numérique, logique, dynamique ou modèle-théorique ;
- prétendre que toute formalisation possible de Lyapunov est incapable
  d'encoder une frontière enrichie ; le résultat exact concerne les vues qui
  se factorisent par `nextDiscoveryProjection` et omettent ainsi l'histoire des
  décisions, la provenance et les témoins de stabilisation ;
- identifier les alternatives absorbées ;
- convertir les témoins constitutifs en hypothèses externes ;
- introduire `Classical`, `noncomputable`, `axiom`, `sorry`, `propext` ou
  `Quot.sound`.

## 15. Fichiers attendus

Ajout permanent :

```text
RelationalPerimeter/Computation/ConstitutiveSearch/
  EndogenousDecomposition/OperationalStability.lean
RelationalPerimeter/Computation/ConstitutiveSearch/
  EndogenousDecomposition/ProjectedStabilizationBoundary.lean
```

Modifications attendues :

```text
RelationalPerimeter/Computation/ConstitutiveSearch/
  EndogenousDecomposition/ConstitutiveFeedback.lean
RelationalPerimeter/Computation/ConstitutiveSearch/
  EndogenousDecomposition/ConstitutiveResolution.lean
RelationalPerimeter/Computation/EndogenousOperationalDecomposition.lean
Tests/ConstitutiveExecutionRegression.lean
Tests/PublicRootImport.lean
README.md
docs/endogenous-operational-decomposition.en.md
docs/decomposition-operationnelle-endogene.fr.md
docs/figures/endogenous-operational-decomposition.svg   # si utile
```

### Ordre d'implémentation et gates intermédiaires

1. Enregistrer le commit de base, l'état Git et les empreintes des quatre
   fichiers fondateurs ; exécuter la suite de vérification avant modification.
2. Ajouter `operationalAbsorption` au rôle existant, mettre à jour son unique
   constructeur canonique et son bloc d'audit, puis compiler
   `ConstitutiveFeedback.lean` isolément.
3. Créer `OperationalStability.lean` avec les frontières typées, les deux
   préservations dérivées, la trace exacte, les théorèmes de longueur et de
   borne, le raccord quantitatif et le certificat intégré ; compiler et lire
   chaque sortie d'audit.
4. Créer `ProjectedStabilizationBoundary.lean` avec le témoin positif, la
   réfutation bloquée, les profils calculables, les deux non-factorisations et
   leurs versions pour toute vue ultérieure ; compiler et lire les audits.
5. Remonter les deux certificats dans `ConstitutiveResolution`, puis dans le
   paquet par entrée, sans ajouter de compte au ledger et sans exécuter une
   seconde histoire pour produire la stabilité publique.
6. Exposer l'API publique, compiler depuis la racine `RelationalPerimeter`, puis
   ajouter les tests de régression et la gate d'import public.
7. Mettre à jour les deux documents, le README et seulement le SVG
   computationnel. Vérifier les liens et la parité des versions française et
   anglaise.
8. Exécuter les builds et scripts complets, rescanner les axiomes et mots-clés
   interdits, comparer les empreintes fondatrices, recalculer le manifeste et
   vérifier l'arbre final.
9. Supprimer le présent document de chantier avant toute fusion. Aucun commit,
   push ou merge ne doit être effectué sans demande explicite.

Document temporaire à supprimer avant fusion :

```text
OPERATIONAL_STABILITY_TARGET.md
```

## 16. Critères d'acceptation

La tâche est terminée seulement si toutes les conditions suivantes sont
remplies.

### Contenu formel

- [ ] Chaque étape de l'histoire causale fournit un témoin de préservation issu
      de sa découverte réelle.
- [ ] Le témoin d'absorption relie explicitement la frontière ouverte à deux
      alternatives à la frontière retenue à une obligation.
- [ ] La chaîne récursive de rôles et ses témoins restent construits dans
      `Type`.
- [ ] Les largeurs `1`, `2`, `1` sont les longueurs des frontières typées de
      l'étape, pas des constantes sans raccord.
- [ ] La trace de largeur est dérivée de la chaîne de rôles de l'histoire faisant
      autorité.
- [ ] La forme exacte de la trace alternée est démontrée.
- [ ] Sa longueur exacte est démontrée.
- [ ] Toute largeur est classée en `1` ou `2`.
- [ ] La borne uniforme `≤ 2` est démontrée.
- [ ] La largeur de la frontière retenue est raccordée à la largeur initiale de
      la queue dépendante sans identifier leurs carriers.
- [ ] La constitution retenue construit positivement un témoin dans `Type` qui
      contient le stage exécuté, son rôle stabilisateur et son certificat.
- [ ] La constitution bloquée ne peut contenir aucun témoin de ce type.
- [ ] Les deux constitutions partagent les données lues par
      `nextDiscoveryProjection`.
- [ ] Cette projection lit effectivement l'affectation, la génération et la
      graine ; sa non-constance est prouvée sur un état canonique de référence
      appartenant au même domaine.
- [ ] Les profils retenu et bloqué valent respectivement `some [1, 2, 1]` et
      `none`, et le premier est calculé depuis les frontières typées.
- [ ] `OperationalStabilizationAvailable` ne se factorise pas par cette
      projection.
- [ ] `operationalStabilizationProfile` ne se factorise pas par cette
      projection.
- [ ] Les deux non-factorisations sont généralisées à toute vue calculée
      uniquement depuis `nextDiscoveryProjection`.
- [ ] La documentation distingue explicitement l'état bloqué contrefactuel des
      états émis par l'exécution faisant autorité.
- [ ] Le certificat de stabilité couvre chaque étape exécutée ; le certificat
      de projection, distinct, établit les deux non-factorisations sur le
      séparateur causal.
- [ ] Le paquet final d'évidence contient les deux certificats.
- [ ] L'API publique expose les certificats et leurs projections.
- [ ] L'API publique nomme explicitement la stabilité opérationnelle endogène.
- [ ] Aucune preuve n'utilise une trajectoire parallèle à la place du `run`
      intégré.

### Constructivité et compilation

- [ ] Chaque fichier Lean modifié contient exactement un bloc d'audit à sa fin.
- [ ] Toutes les nouvelles déclarations principales sont auditées.
- [ ] Aucun audit ne rapporte d'axiome.
- [ ] Le dépôt ne contient aucun `noncomputable`.
- [ ] Aucun `axiom`, `sorry`, `Classical`, `propext` ou `Quot.sound` n'est
      introduit.
- [ ] `lake clean` réussit.
- [ ] `lake build +RelationalPerimeter` réussit.
- [ ] `lake build` réussit.
- [ ] `scripts/verify.ps1` réussit.
- [ ] `scripts/verify.sh` réussit.
- [ ] `git diff --check` réussit.

### Régressions et publication

- [ ] Les tests protègent la provenance réelle du témoin de stabilité.
- [ ] Les tests protègent le raccord entre cible retenue, sortie exécutée et état
      suivant.
- [ ] Les tests protègent la borne de largeur sur l'histoire publique.
- [ ] Les tests protègent la construction du témoin retenu, l'impossibilité du
      témoin bloqué et leur non-factorisation par l'état projeté.
- [ ] Les tests protègent les valeurs exactes des deux profils et leur
      non-factorisation par l'état projeté.
- [ ] Les tests protègent les versions paramétrées par une vue arbitraire de
      l'état projeté.
- [ ] L'import public donne accès au nouveau résultat.
- [ ] Les quatre fichiers fondateurs restent inchangés octet pour octet.
- [ ] Les versions française et anglaise sont cohérentes.
- [ ] Les documents situent la notion par rapport aux stabilités classiques
      sans revendiquer une équivalence qui n'est pas formalisée.
- [ ] Les liens documentaires locaux sont valides.
- [ ] Aucun cache ni artefact généré n'est ajouté à Git.
- [ ] Le document de chantier présent est supprimé avant la fusion.

## 17. Verdict attendu à la fin de la branche

Le verdict final doit pouvoir être formulé sans extrapolation :

> **For every executed history in the constructed family, each operational
> stage carries the preservation witness reconstructed from its own discovery.
> The resulting operational width trace has exactly `2 * n + 1` entries and is
> uniformly bounded by `2`. Structural multiplicity is therefore prevented
> from accumulating as exponential operational width, while the alternatives
> remain structurally distinct. This is an endogenous operational stability:
> the executed computation preserves its criterion while constituting which
> alternatives continue as independent obligations. In the causal separator,
> the retained and counterfactually blocked constitutions share the projected
> assignment, generation and search seed, while the first positively constructs
> a complete stabilization witness and the second admits none. Their calculable
> stabilization profiles are respectively `some [1, 2, 1]` and `none`.
> Consequently, neither stabilization availability nor stabilization profile
> factors through the projected state data, or through any further view computed
> solely from those data.**

Cette formulation doit être une lecture directe du paquet public d'évidence,
et non une interprétation ajoutée après coup à des théorèmes dispersés.
