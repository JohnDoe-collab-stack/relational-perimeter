# Cible terminale — Alignement constitutif neuronal incrémental

## Statut du document

Ce document fixe la cible terminale du chantier d’alignement neuronal dans le
cadre relationnel constitutif. Il s’agit d’une spécification de travail et non
d’un claim déjà démontré.

Les résultats actuellement présents dans le dépôt constituent le socle de la
cible. Ils ne doivent ni être affaiblis, ni être renommés pour donner
l’impression que la cible terminale est déjà atteinte.

La cible ne consiste pas à choisir des valeurs humaines, à apprendre un contrat
normatif ou à déclarer qu’un comportement observé est souhaitable. Le
méta-contrat constitutif est fixé avant l’exécution. Il détermine les contrats
opérationnels admissibles et les transitions autorisées entre eux. Un contrat
opérationnel ne peut changer que par une transition elle-même certifiée par ce
méta-contrat. Le problème traité est celui de la production, de la conservation
et du contrôle effectifs de ces obligations à travers le mécanisme neuronal et
ses reconfigurations.

Le raccord constitutif explicité dans ce plan est obligatoire. Il complète les
exigences existantes sans en supprimer ni en restreindre aucune. Il distingue
le schéma reçu, son instanciation sur la production exécutée et les contraintes
de préservation démontrées à partir de cette même production. Son inscription
est une obligation de travail, pas une déclaration de réalisation dans le code.

## Objectif terminal

Construire un runtime exécutable et un théorème Lean garantissant que, pour un
artefact neuronal admissible, un méta-contrat constitutif exécutable et toute
suite finie de reconfigurations, aucune action ni mise à jour ne peut être
effectuée si la chaîne constitutive exigée n’est pas certifiée sur les
occurrences réellement produites. Cette garantie couvre les changements de
contrat opérationnel autorisés par le méta-contrat fixé.

Lorsque l’état initial et chaque reconfiguration sont acceptés, toute étape
exécutée doit satisfaire simultanément les propriétés suivantes.

1. L’exigence et le contexte courants sont reçus puis encodés par l’exécution.
2. La transformation neuronale est celle calculée par le run maître.
3. La proposition est dérivée de cette transformation et du décodeur fixé.
4. L’action est dérivée de la proposition selon le contrat d’action.
5. L’effet et le successeur sont ceux effectivement produits par cette action.
6. Toute reconfiguration dépend causalement du système antérieur, de la nouvelle
   exigence et de l’autorisation incorporée.
7. Le système transmis à l’étape suivante est exactement celui produit par la
   reconfiguration précédente.
8. Une information historique ne peut disparaître que par une opération
   d’oubli exécutée.
9. Cet oubli conserve exactement tous les futurs couverts par le contrat.
10. Toute mise à jour qui rompt l’une de ces obligations est refusée avant son
    effectuation.

La forme finale attendue est :

```lean
theorem checkedTrace_constitutivelyAligned
    (artifact : SerializedNetwork)
    (meta : ConstitutiveMetaContract)
    (contract : ConstitutiveContract)
    (admitted : meta.Admits contract)
    (initial :
      checkInitial meta contract admitted artifact = .ok checkedInitial)
    (updates : List SerializedNeuralUpdate)
    (trace :
      checkUpdates checkedInitial updates = .ok checkedTrace) :
    EveryExecutedStepSatisfies meta checkedTrace.execution
```

La quantification porte sur toute trace finie acceptée. Elle ne doit pas être
remplacée par une trace exemple de longueur fixée.

## Critère scientifique discriminant

La cible ne sera pas fermée par la seule certification d’un agent construit
pour réussir le test. Il faut établir un gain propre par rapport à une lecture
exclusivement extensionnelle du comportement courant.

Le test doit porter sur le vérificateur de mise à jour et non seulement sur le
vérificateur initial. Un même agent initial doit d’abord être accepté. Deux
mises à jour partageant la même intention opérationnelle admise sont ensuite
construites :

- `alignedUpdate`, dont le résultat est produit par la chaîne constitutive
  exigée ;
- `bypassUpdate`, qui produit le même comportement courant par un raccourci ne
  consommant pas réellement l’une des ressources imposées.

L’admission de l’intention de mise à jour reste distincte de la certification
de son résultat. Le runtime doit accepter `alignedUpdate` et refuser
`bypassUpdate` avant toute effectuation. Ils doivent satisfaire :

```lean
theorem candidateCurrentBehaviorEquivalent :
    forall input : DeclaredCurrentInput contract,
      currentBehavior
          (simulateUncheckedUpdate checkedInitial alignedUpdate) input =
        currentBehavior
          (simulateUncheckedUpdate checkedInitial bypassUpdate) input
```

`simulateUncheckedUpdate` est une sémantique pure utilisée uniquement pour
établir le contre-factuel. Elle n’est pas une entrée publique du runtime et ne
peut produire aucun effet. Un futur fini explicite doit conserver le contrat
pour le résultat de `alignedUpdate` et révéler la violation qu’aurait produite
`bypassUpdate` si elle avait été exécutée. `FutureViolationWitness` contient la
liste non vide exacte des requêtes, les deux résultats calculés et la preuve de
leur incompatibilité avec le contrat opérationnel proposé par la mise à jour.

Le théorème discriminant attendu est :

```lean
theorem constitutiveChecker_detectsLatentBypass :
    checkInitial meta contract admitted initialArtifact =
      .ok checkedInitial ∧
    SameAdmittedUpdateIntent alignedUpdate bypassUpdate ∧
    CurrentBehaviorEquivalentAfterUpdate
      checkedInitial alignedUpdate bypassUpdate ∧
    EveryCurrentExtensionalVerifierAgrees
      checkedInitial alignedUpdate bypassUpdate ∧
    checkUpdate checkedInitial alignedUpdate = .ok alignedNext ∧
    checkUpdate checkedInitial bypassUpdate =
      .error .missingConstitutiveDependency ∧
    FutureViolationWitness
      (simulateUncheckedUpdate checkedInitial bypassUpdate) ∧
    RejectedBeforeEffect checkedInitial bypassUpdate
```

`EveryCurrentExtensionalVerifierAgrees` doit être indexé par une définition
précise d’un vérificateur extensionnel, à savoir un vérificateur dont le verdict
se factorise uniquement par le comportement courant observé sur un domaine
fini explicitement déclaré. Il ne doit pas être présenté comme un résultat sur
toute méthode de vérification imaginable. La preuve que ces vérificateurs
agréent est une conséquence de la factorisation et de l’équivalence courante ;
elle ne constitue pas à elle seule le claim de nouveauté.

## Objets formels requis

### Artefact neuronal autonome

L’artefact reçu ne doit pas être un `NetworkProgram` écrit spécialement dans la
preuve. Il faut une représentation de données autonome et décodable.

```lean
inductive SerializedSource
  | receivedInput (index : Nat)
  | priorNeuron (index : Nat)

structure SerializedWeightedInput where
  source : SerializedSource
  weight : Int

structure SerializedNeuron where
  inputs : List SerializedWeightedInput
  bias : Int
  threshold : Int

structure SerializedNetwork where
  inputCount : Nat
  neurons : List SerializedNeuron
  outputs : List Nat
```

Le décodeur doit vérifier les indices, la non-vacuité des sorties et la
stratification chronologique avant de produire le programme dépendant. Une
référence `.priorNeuron i` n’est valide que lorsque `i` désigne un neurone déjà
produit. La notion de couche utilisée dans l’instance scientifique doit être un
readout dérivé explicitement de ce graphe chronologique, et non une information
ajoutée seulement dans la prose.

Le résultat ne peut pas être le seul `NetworkProgram`. Le runtime consomme un
`NativeSystem`, donc l’encodage, les ports de sortie et le décodage doivent être
raccordés au même artefact. Le contrat fournit l’interface d’entrée et de
proposition ; le décodeur construit le programme et ses ports puis prouve leur
correspondance aux données sérialisées.

```lean
structure DecodedNeuralArtifact
    (contract : ConstitutiveContract) where
  private mk ::
  source : SerializedNetwork
  system : NativeSystem
    (RequirementInput contract.family) contract.Proposal
  decodingExact : ArtifactDecodingExact source system

def decodeArtifact
    (contract : ConstitutiveContract)
    (artifact : SerializedNetwork) :
    Except ArtifactError (DecodedNeuralArtifact contract)
```

Le décodage réussi doit fournir les équations nécessaires pour raccorder le
programme, les ports et le système obtenus aux données sérialisées. Ni les
poids, ni les ports, ni le décodeur ne peuvent être remplacés après le
décodage par des valeurs choisies pour faciliter une preuve.

### Contrat constitutif

Le méta-contrat fixe doit distinguer au minimum :

- les contrats opérationnels admissibles ;
- les transitions permises entre deux contrats opérationnels ;
- les preuves qu’une transition conserve les obligations qui doivent survivre
  au changement de contrat ;
- les obligations qui doivent être invalidées et revérifiées après ce
  changement.

Chaque contrat opérationnel doit ensuite distinguer au minimum :

- encodage de l’exigence et du contexte ;
- conditions de causalité pertinentes ;
- préservation proposition–action ;
- admission de l’autorisation ;
- satisfaction par l’effet produit ;
- futurs couverts ;
- informations historiques conservables ou oubliables.

Ces composantes ne doivent pas être compressées en un booléen opaque.

### Raccord constitutif obligatoire — origine et portée des obligations

Le méta-contrat, le schéma d'observation, les exigences et les contextes reçus
restent des entrées explicitement déclarées. L'exécution ne fabrique pas leur
justification normative. Elle produit les occurrences et les relations sur
lesquelles le schéma est instancié, ainsi que les témoins permettant d'établir
les conséquences de préservation. La production seule, sans schéma déclaré,
ne définit pas ce qui doit être conservé.

La construction doit distinguer les trois niveaux suivants :

1. **Reçu et fixé.** Le méta-contrat détermine les schémas admissibles et leurs
   transitions. Pour une comparaison donnée, le schéma d'observation, le
   domaine et les exigences sont fixés indépendamment de la réalisation
   candidate et de son verdict. Les changements restent possibles uniquement
   par les transitions admises déjà exigées, sans adaptation opportuniste.
2. **Instancié et produit.** Selon ce schéma, une construction explicite
   instancie les familles d'obligations du contrat admis sur l'état et les
   occurrences de la production maître. Elle indique quelles données sont
   reçues, lesquelles sont calculées et quels témoins de cette même exécution
   sont effectivement consommés.
3. **Démontré et appliqué.** Les témoins produits certifient les dépendances et
   distinctions pertinentes. Les contraintes de préservation en sont dérivées
   sous le contrat fixé, pour les sources ainsi produites, puis appliquées aux
   réalisations candidates.
   Elles ne sont pas introduites comme des conclusions déjà présentes dans
   les données d'entrée ou choisies pour accepter une représentation.

Techniquement, trois objets restent distincts dans l'API existante :

- le contrat opérationnel `c : ConstitutiveContract`, fourni par le
  méta-contrat admis, fixe les familles d'obligations et le schéma des futurs ;
- les applications `…At state` instancient ces familles sur l'état exact
  produit. Par exemple, le témoin causal a pour type
  `c.causalCondition.Witness (c.causalConditionAt state)` ; il faut en tracer
  la construction et la consommation, pas seulement l'indice ;
- `c.futureContract` est le contrat d'observation, et
  `c.futureSourceOfState state` y raccorde cet état produit. Les conséquences
  universelles de RC4 portent sur les réalisations exactes de ce contrat et
  sur les sources issues de ce raccord.

Instancier les obligations ne requiert donc pas de reconstruire un nouveau
`ConstitutiveContract` à chaque run. Un changement de contrat reste une
transition admise par le méta-contrat, avec les transports et revérifications
déjà exigés. Ces repères désignent les interfaces de
[OperationalContract.lean](../../RelationalPerimeter/Agents/Neural/OperationalContract.lean)
et de [CoveredFutureRealization.lean](../../RelationalPerimeter/Agents/Neural/CoveredFutureRealization.lean),
pas une seconde API à construire.

L'ordre logique obligatoire est : schéma fixé et production exécutée,
obligations instanciées et témoins issus de cette production, contraintes
démontrées, puis examen d'une réalisation. Le sens des obligations sources
n'est défini ni par la projection mémoire candidate, ni par sa preuve
d'exactitude, ni par le succès du contrôle chargé de les vérifier. Les témoins
sources qui fondent les conséquences universelles sont construits sans
recevoir la projection ni supposer l'exactitude de la réalisation candidate
à laquelle ces conséquences seront appliquées.

Cette indépendance n'interdit ni la réutilisation justifiée de certificats
antérieurs, ni la construction d'un témoin par réflexion d'une décision
exécutée, dès lors que l'obligation vérifiée est définie indépendamment de son
succès. Elle n'interdit pas non plus de produire l'état depuis l'artefact
neuronal examiné. Le checker peut évaluer cette production dans sa sémantique
pure, sans effectuer une action refusée. Les certificats de conformité sont
bien calculés depuis les données et l'exécution examinées ; ils ne doivent
pas redéfinir le contrat pour déclarer conforme la sortie observée.

Les six obligations de clôture suivantes sont conjointes :

| Obligation | Évidence exigée |
| --- | --- |
| RC1 — Origine déclarée | Identifier séparément les primitives, exigences, contextes, schémas reçus et lois d'admission. Ne pas présenter une norme reçue comme produite ou justifiée par l'exécution. |
| RC2 — Instanciation authentique | Instancier les familles d'obligations sur l'état et les occurrences exactes du même run, avec leurs équations de production, leurs témoins et leurs consommateurs. Un champ stocké ou un résultat reconstruit indépendamment ne suffit pas. |
| RC3 — Indépendance de la réalisation | Exposer les types, producteurs et dépendances excluant une obligation source définie par la projection à valider ou par le succès de son propre contrôle. Les témoins sources fondant les conséquences universelles sont construits sans recevoir la projection ni supposer l'exactitude candidate. Les certificats antérieurs et la réflexion d'une décision restent utilisables sous les conditions ci-dessus. Un schéma paramétrique conserve ses paramètres déclarés. |
| RC4 — Conséquences générales démontrées | Pour `c.futureContract` fixé et les sources issues de la production, démontrer les contraintes observables certifiées pour tout type mémoire `M` et toute `ExactRealization c.futureContract M`. La séparation éventuelle est une conclusion depuis un témoin de distinction, jamais un champ supposé de l'exactitude. |
| RC5 — Transport au fil des transformations | Raccorder ces obligations aux transformations neuronales, au décodeur, à l'action, au successeur, à la mémoire et aux transitions de contrat. Consommer les certificats exacts, transporter les obligations persistantes et revérifier celles invalidées avant effectuation. |
| RC6 — Réalisations positives et prévention | Fermer ce raccord sur les constructions positives non identitaires, les reconfigurations successives et l'oubli non trivial exigés, avec une réalisation exacte témoin du contrat concerné, puis sur le rejet du contournement. Un refus universel ou une seule obstruction ne satisfait pas ce critère. |

RC4 réutilise l'API de futurs et de réalisations exactes du dépôt, sans second
runtime. Le lemme générique `ExactRealization.distinct_memory_of_separator`
est réutilisé lorsqu'un séparateur est construit ; il n'est pas à redémontrer.
Le travail requis porte sur le raccord neuronal, ses témoins issus de la
production et ses consommateurs. Sa quantification sur les réalisations
s'ajoute à celle portant sur toutes les traces finies acceptées ; aucune ne
remplace l'autre. Elle ne postule ni injectivité globale, ni quotient canonique,
ni interdiction de tout
regroupement. Une dépendance causale certifiée ne devient pas automatiquement
un séparateur de futurs : il faut construire le raccord aux observations du
contrat et, lorsqu'une séparation est revendiquée, fournir son témoin fini.
Les autres exigences causales restent à démontrer dans leur propre interface.
La préservation dirigée des transformations ne doit pas être renforcée
artificiellement en transport réversible ou en égalité de tous les types.

Les contrôles locaux doivent viser les substitutions suivantes : contrat
réécrit après lecture du candidat, obligation définie par le succès du
checker, témoin emprunté à une autre occurrence, distinction nécessaire
effacée sans transport et certificat réutilisé sous un contrat changé sans
justification. Les tests existants peuvent couvrir ces cas si leur obligation
exacte est atteinte. Les signatures et dépendances formelles établissent la
généralité ; les fixtures ne la remplacent pas.

Gödel est un cas extrême où une combinaison de regroupement et de préservation
est impossible. Il n'est ni une étape, ni une prémisse, ni une dépendance
diagonale requise pour le résultat neuronal. Ici, le raccord doit d'abord
permettre les transformations, reconfigurations et oublis admissibles, puis
prévenir leurs violations. Aucun témoin gödelien, énoncé indécidable ou rejet
diagonal n'est exigé pour fermer RC1–RC6. Les résultats Gödel et Tarski déjà
présents restent protégés par l'exigence de non-régression.

### Domaine décidable et base causale finie

Le vérificateur ne peut pas rechercher une valeur d’intervention arbitraire
dans `Int`. Le contrat opérationnel doit donc déclarer un domaine fini
d’observation et une base finie d’interventions candidates pour chaque port
contrôlé.

```lean
structure FiniteCausalBasis
    (contract : ConstitutiveContract)
    (artifact : DecodedNeuralArtifact contract) where
  currentInputs : List (RequirementInput contract.family)
  currentInputsComplete : CoversDeclaredCurrentDomain currentInputs
  replacements : StableNodeId artifact -> List Activation
  replacementCoverage : CoversDeclaredCausalCondition replacements
```

La complétude du checker est relative à ce domaine déclaré et à cette base.
Elle ne doit pas être étendue à toutes les valeurs entières ni à toute propriété
sémantique possible. Les égalités nécessaires doivent disposer d’instances
décidables explicites, et chaque décision positive doit être reliée par un
lemme de réflexion au certificat propositionnel qu’elle construit.

### État vérifié

```lean
structure CheckedAgent
    (meta : ConstitutiveMetaContract)
    (contract : ConstitutiveContract) where
  private mk ::
  contractAdmitted : meta.Admits contract
  artifact : DecodedNeuralArtifact contract
  state : ReconfiguredExecutionState contract.family
  certificate : StateConstitutiveCertificate contract artifact state
```

Le constructeur doit être privé. Les seules entrées publiques doivent provenir
du vérificateur initial ou d’une mise à jour vérifiée.

### Mise à jour neuronale

Une mise à jour sérialisée doit décrire explicitement ce qu’elle remplace :

- paramètres neuronaux ;
- arêtes ;
- ports ;
- décodeur ;
- ressource d’autorisation ;
- projection mémoire ;
- contrat opérationnel, uniquement lorsque le changement est accompagné d’une
  transition admise par le méta-contrat fixe.

Une mise à jour ne peut pas recevoir directement son propre certificat. Les
identifiants d’occurrences qu’elle mentionne doivent être stables et le
décodeur de delta doit produire une correspondance validée entre l’ancien et le
nouveau programme. Une suppression, insertion ou réindexation non couverte par
cette correspondance invalide les fragments concernés.

### Vérificateur exécutable

```lean
inductive AlignmentError
  | malformedArtifact
  | invalidStableNodeMapping
  | inadmissibleContract
  | unauthorizedContractTransition
  | missingRequirementDependency
  | missingContextDependency
  | missingAuthorizationDependency
  | zeroWeightDependency
  | transformationMismatch
  | proposalMismatch
  | actionContractViolation
  | successorMismatch
  | futureContractViolation
  | historyAlreadyForgotten

def checkInitial
    (meta : ConstitutiveMetaContract)
    (contract : ConstitutiveContract)
    (admitted : meta.Admits contract)
    (artifact : SerializedNetwork) :
    Except AlignmentError (CheckedAgent meta contract)

structure CheckedUpdate
    {meta : ConstitutiveMetaContract}
    {currentContract : ConstitutiveContract}
    (current : CheckedAgent meta currentContract)
    (update : SerializedNeuralUpdate)
    (nextContract : ConstitutiveContract) where
  private mk ::
  next : CheckedAgent meta nextContract
  transition : meta.AllowsTransition currentContract nextContract
  execution : ExecutedCertifiedUpdate current update next

def checkUpdate
    {meta : ConstitutiveMetaContract}
    {currentContract : ConstitutiveContract}
    (current : CheckedAgent meta currentContract)
    (update : SerializedNeuralUpdate) :
    Except AlignmentError
      (Sigma fun nextContract =>
        CheckedUpdate current update nextContract)
```

La correction doit être prouvée :

```lean
theorem checkInitial_sound : ...
theorem checkUpdate_sound : ...
theorem checkUpdates_sound : ...
```

La correction doit relier le résultat précis retourné au certificat précis
consommé par l’exécution. Elle ne doit pas conclure seulement qu’un certificat
quelconque existe.

Une complétude relative est exigée uniquement pour les conditions décidables
que le vérificateur annonce vérifier :

```lean
def UpdateAccepted
    (agent : CheckedAgent meta contract)
    (update : SerializedNeuralUpdate) : Prop :=
  Exists fun result => checkUpdate agent update = .ok result

theorem checkUpdate_complete_for_local_conditions :
    UpdateAccepted agent update ↔
      LocalDecidableConstitutiveConditions agent update
```

Il est interdit de transformer cette complétude relative en une décision de
toute propriété sémantique possible d’un agent.

### Trace vérifiée

```lean
inductive CheckedReconfigurationTrace
    (meta : ConstitutiveMetaContract) :
    {contract : ConstitutiveContract} →
    CheckedAgent meta contract →
    List SerializedNeuralUpdate → Type
  | nil (current : CheckedAgent meta contract) :
      CheckedReconfigurationTrace meta current []
  | step
      (checked : CheckedUpdate current update nextContract)
      (tail : CheckedReconfigurationTrace meta checked.next rest) :
      CheckedReconfigurationTrace meta current (update :: rest)
```

Chaque `step` doit consommer le `next` produit par l’étape précédente. Une
reconstruction indépendante d’un état extensionnellement égal est interdite.

### Fermeture de l’API d’exécution

La propriété « aucune mise à jour non certifiée n’est effectuée » exige plus
qu’un théorème sur `checkUpdate`. L’état exécutable du runtime doit avoir un
constructeur privé, et son unique opération publique de reconfiguration doit
appeler le checker puis consommer le `CheckedUpdate` exactement retourné.

```lean
structure CertifiedRuntime (meta : ConstitutiveMetaContract) where
  private mk ::
  currentContract : ConstitutiveContract
  current : CheckedAgent meta currentContract

def submitUpdate :
    CertifiedRuntime meta → SerializedNeuralUpdate →
    Except AlignmentError (CertifiedRuntime meta)
```

Un théorème d’accessibilité doit établir que tout état atteignable par cette API
possède une trace `CheckedReconfigurationTrace`. Aucun exécuteur public ne doit
accepter directement un `SerializedNeuralUpdate` ou un artefact décodé sans le
certificat correspondant. La sémantique contre-factuelle non vérifiée reste
pure et séparée de cette API.

## Corrections préalables du socle actuel

### Authenticité de la transformation neuronale

`ExecutedSignalTransformation` ne peut plus recevoir une fonction arbitraire
et seulement vérifier son égalité ponctuelle avec la cible.

La nouvelle construction doit être scellée et dérivée de :

- `NativeRun.trace` ;
- `NetworkProgram.neuronAt` ;
- `NativeTrace.activationsBefore` ;
- `fireNeuron` ;
- une arête `EffectiveReadsFrom` ;
- l’occurrence source et l’occurrence cible exactes.

Le dépôt possède déjà le raccord essentiel :

```lean
NativeTrace.neuron_output_exact
```

Le transformateur local doit être calculé en remplaçant uniquement la valeur de
l’occurrence source dans l’environnement exact disponible avant le neurone
cible. Les autres entrées du neurone restent celles du même run.

La valeur cible doit être une conclusion de cette exécution et non un paramètre
permettant de fabriquer :

```lean
fun _ => target.value
```

Fixture obligatoire :

```text
PostHocConstantTransformCannotWitnessExecution
```

### Oubli réellement exécuté

L’origine doit être présente dans l’état opérationnel antérieur à l’oubli.

```lean
structure HistoricalOperationalState where
  origin : History
  current : ReconfiguredExecutionState family
```

Pour deux origines distinctes, il faut établir avant l’oubli :

```lean
leftBefore ≠ rightBefore
```

et, lorsque le contrat l’autorise, après exécution :

```lean
forget leftBefore = reduced
forget rightBefore = reduced
```

L’égalité terminale ne doit plus être obtenue en commençant par
`Agent.initial_memories_equal`. Elle doit résulter du programme d’oubli exécuté
sur deux états historiquement distincts.

Fixtures obligatoires :

```text
AlreadyForgottenInputCannotWitnessExecutedForgetting
ConstantProjectionCannotWitnessExecutedForgetting
ReducedMemoryCannotReplaceHistoricalOperationalState
```

## Conservation exacte des futurs

Une simple égalité des deux mémoires réduites ne suffit pas à justifier la
projection. Il faut construire les lois locales de simulation du contrat puis
les assembler dans l’API `ExactRealization` déjà présente. Le chantier ne doit
pas créer un second runtime de futurs parallèle.

```lean
structure FutureContractSimulationData where
  forward : ...
  backward : ...
  backwardForward : ...
  forwardBackward : ...
  nextExact : ...
  eventExact : ...
  readExact : ...

def FutureContractSimulationData.toExactRealization :
    FutureContractSimulationData sourceContract reducedContract project →
    ExactRealization sourceContract ReducedMemory
```

Puis :

```lean
theorem simulation_preserves_every_finite_future
    (simulation : FutureContractSimulationData
      sourceContract reducedContract project) :
    forall requests,
      sourceContract.outcome source requests =
        reducedContract.outcome (project source) requests
```

La preuve doit être obtenue par `ExactRealization.outcome_exact`, dont
l’induction porte sur la liste des requêtes. Une collection d’exemples de
futurs ne peut pas remplacer ce théorème.

## Vérification incrémentale

### Cône causal affecté

Les dépendances neuronales sont extraites des `WeightedInput`, mais elles ne
suffisent pas. Le graphe incrémental doit couvrir toute la chaîne : entrées
reçues, neurones, ports de sortie, décodeur, proposition, action, effet,
successeur, projection mémoire et observations contractuelles. Une modification
du décodeur ou du contrat doit donc affecter les nœuds aval correspondants même
si aucune arête neuronale ne change.

Les nœuds possèdent des identifiants stables indépendants de leurs indices
`Fin`. Chaque delta construit une correspondance partielle validée entre les
nœuds de l’ancien et du nouveau système. Pour une mise à jour `update`, le
runtime calcule :

```lean
affectedConstitutiveCone oldArtifact newArtifact updateCorrespondence
```

Le cône contient les occurrences modifiées et toutes leurs dépendances aval
dans ce graphe hétérogène. Tout nœud sans correspondance stable est affecté par
définition. Un changement de contrat invalide également toutes les obligations
que la transition de méta-contrat ne transporte pas explicitement.

### Réutilisation des certificats

```lean
theorem outsideAffectedCone_unchanged :
    node ∉ affectedConstitutiveCone oldArtifact newArtifact correspondence →
    oldObservation node =
      newObservation (correspondence.transport node)

theorem reuseUnaffectedCertificate :
    Unaffected certificateFragment correspondence →
    ValidInUpdatedSystem
      (transportCertificateFragment correspondence certificateFragment)
```

Le certificat global suivant doit être composé de :

- fragments inchangés réutilisés ;
- fragments du cône causal recalculés ;
- obligations contractuelles affectées revérifiées.

Une pseudo-réutilisation qui rejoue toute l’histoire puis renomme le résultat
« incrémental » est interdite. Le certificat incrémental doit conserver les
fragments anciens comme données effectivement consommées, compter séparément
les fragments transportés et recalculés, et exposer un théorème d’égalité avec
la certification complète du nouveau système.

## Instance scientifique indépendante

L’instance terminale ne peut pas être le réseau public minimal actuel ni un
réseau écrit à la main pour satisfaire directement les obligations de preuve.

Elle doit être obtenue par un protocole externe reproductible d’apprentissage
ou de transformation d’un modèle appris, puis intégrée sous une forme locale
autonome et munie d’une empreinte. Le protocole fixe le générateur, les données
ou leur empreinte, les paramètres, les graines, les commandes et la procédure
de normalisation avant la production confirmatoire. Aucune retouche manuelle
des poids destinée à simplifier les preuves n’est admise. Les matériaux bruts
extérieurs restent hors du dépôt conformément à la procédure scientifique.

L’artefact normalisé doit comporter :

- plusieurs couches ;
- plusieurs chemins causaux ;
- plusieurs exigences et contextes ;
- une autorisation effective ;
- un chemin de contournement possible ;
- plusieurs sorties ou plusieurs observations contractuelles ;
- plusieurs reconfigurations successives.

Les poids ne doivent pas être choisis dans les corps de preuve. Les certificats
ne doivent pas être écrits poids par poids. Le vérificateur doit les produire à
partir de l’artefact décodé. L’import doit conserver la correspondance avec
l’artefact externe et enregistrer son empreinte, sa provenance, ses conditions
de réemploi et le protocole qui l’a produit.

## Expérience de séparation

À partir du même agent initial certifié et du même protocole figé, produire :

1. l’artefact initial accepté ;
2. une intention de mise à jour admise ;
3. `alignedUpdate` et `bypassUpdate`, partageant cette intention ;
4. la preuve de l’équivalence comportementale courante de leurs résultats
   simulés sur le domaine déclaré ;
5. la certification et l’exécution de `alignedUpdate` ;
6. le rejet de `bypassUpdate` au diagnostic causal exact ;
7. un futur fini explicite certifiant la divergence contractuelle qu’aurait
   produite son exécution non vérifiée ;
8. la preuve que le runtime refuse la mise à jour avant tout effet ;
9. la preuve qu’aucun vérificateur se factorisant uniquement par le comportement
   courant déclaré ne peut distinguer ces deux candidats.

Les mutations négatives minimales sont :

- suppression de l’arête d’autorisation ;
- substitution du contexte ;
- substitution de l’exigence ;
- court-circuit du système antérieur ;
- transformateur constant reconstruit après coup ;
- arête de poids nul ;
- pré-effacement de l’histoire ;
- reconstruction indépendante du successeur.

Chaque fixture doit atteindre l’obligation visée avec son diagnostic, sa ligne,
sa colonne et son rôle scientifique exacts.

## Comparaison de capacité obligatoire

La qualification de résultat nouveau ne peut pas reposer sur la seule réunion
de mots connus. Une matrice comparative doit fixer les classes de méthodes et
les capacités examinées avant l’expérience confirmatoire.

Au minimum, elle compare séparément :

- vérification extensionnelle du comportement courant ;
- analyse causale interventionnelle d’un réseau fixe ;
- shielding ou certification d’actions avant exécution ;
- systèmes auto-adaptatifs avec garanties ;
- vérification neuronale incrémentale avec réutilisation de preuves ;
- propagation de certificats dans une chaîne de déploiement.

Le résultat propre à établir n’est pas qu’aucune de ces familles ne possède une
de ses composantes. Il est que le runtime constitutif réalise sur la même trace
la conjonction suivante : provenance causale neuronale, admission distincte de
la certification, action et effet exacts, succession produite, oubli exact,
préservation de tous les futurs, refus pré-effectuation et réutilisation locale
de certificats.

La comparaison doit comporter :

1. les définitions exactes des interfaces comparées ;
2. un théorème de limitation uniquement pour la classe extensionnelle définie
   par factorisation ;
3. une expérience sur le même artefact et les mêmes mises à jour pour les
   autres baselines exécutables ;
4. l’identification explicite de la capacité absente ou non certifiée dans
   chaque baseline ;
5. l’interdiction de transformer l’absence d’une fonction dans un outil donné
   en impossibilité universelle.

Une simple détection locale par intervention ne remplace pas le théorème sur
toute trace de reconfiguration. Réciproquement, la présence de la trace ne doit
pas être présentée comme une nouvelle méthode de causalité si elle ne fait que
réutiliser une certification déjà connue.

## Passage à l’échelle

Définir une famille paramétrée d’artefacts et figer avant les runs
confirmatoires :

- générateur ;
- paramètres ;
- tailles ;
- graines éventuelles ;
- commandes ;
- empreintes ;
- protocole de mesure.

Le générateur doit produire avec chaque artefact une preuve ou un contrôle
rejouable de bonne formation. La famille ne doit pas être obtenue en recopiant
plusieurs fois une instance fixe sans augmenter le graphe causal pertinent.

Mesurer séparément :

- taille du réseau ;
- taille du cône causal affecté ;
- longueur de la trace de reconfiguration ;
- taille du certificat initial ;
- taille du delta de certificat ;
- temps d’exécution ;
- temps de vérification initiale ;
- temps de revérification incrémentale ;
- temps de revérification complète de la même propriété sur le même artefact ;
- nombre de fragments réellement réutilisés et réellement recalculés.

Le claim principal reste un théorème. Les mesures servent à établir la portée
pratique et ne deviennent pas une preuve de généralité. L’incrémentalité n’est
revendiquée comme gain pratique que si le protocole montre une réduction face à
la revérification complète sans changer la propriété vérifiée.

## Réutilisation du code existant

Les composants suivants forment le socle à conserver et à renforcer :

| Composant existant | Rôle dans la cible terminale |
| --- | --- |
| `NativeTrace` | trace maître co-produite avec les activations |
| `NativeTrace.neuron_output_exact` | authenticité de chaque sortie neuronale |
| `EffectiveReadsFrom` | dépendance structurelle non nulle |
| `CausalRole` | intervention et propagation jusqu’à la proposition |
| `CertifiedReconfiguration` | paquet local de reconfiguration |
| `ReconfiguredCausalStage` | étape causale exacte |
| `ReconfiguredInteractionHistory` | composition sur toute trace finie |
| `FutureContract` | sémantique des futurs couverts |
| `ExactRealization` | transport exact des futurs |
| `ConstitutiveAlignmentCertificate` | noyau du certificat terminal |

Les modifications doivent renforcer ces raccords. Elles ne doivent pas créer un
second runtime parallèle ou reconstruire indépendamment leurs sorties.

## Ordre d’implémentation obligatoire

```text
authenticité C3
→ oubli C8
→ régression C1–C17 complète
→ commit scientifique stable et gates fraîches du socle

→ méta-contrat et transitions de contrats opérationnels
→ schéma contractuel et provenance des obligations explicités (RC1, RC3)
→ représentation sérialisée et décodage du NativeSystem complet
→ domaine décidable et base causale finie
→ obligations instanciées sur l'état produit et témoins du run maître (RC2)
→ ExactRealization et tous les futurs
→ raccord au futureContract fixé et contraintes pour toute réalisation exacte (RC4)
→ StateConstitutiveCertificate
→ CheckedAgent et CheckedUpdate

→ vérificateur initial
→ vérificateur de mise à jour complet de référence

→ identifiants stables et correspondance entre versions
→ graphe causal constitutif hétérogène
→ calcul du cône affecté
→ réutilisation locale réellement transportée
→ vérificateur de mise à jour incrémental
→ équivalence entre vérification incrémentale et vérification complète
→ consommation et transport du raccord constitutif à chaque transition (RC5)

→ checkUpdates et trace finie dépendante vérifiée
→ API runtime fermée
→ théorème d’accessibilité de tous les états du runtime

→ protocole comparatif et baselines figés
→ artefact appris indépendant
→ séparation alignedUpdate/bypassUpdate
→ témoin fini de divergence contrefactuelle
→ raccord fermé sur les instances positives et le refus pré-effectuation (RC6)
→ campagne finale de mutations négatives
→ passage à l’échelle et comparaison avec le recheck complet

→ texte et claim scientifiques figés
→ commit d’évidence stable
→ gates complètes sur cette révision
→ audit indépendant de validité
→ audit comparatif indépendant de portée et nouveauté
→ finalisation du registre et des rapports
→ gates finales de livraison
```

Il est interdit d’enregistrer le claim terminal avant l’artefact indépendant et
la séparation `alignedUpdate`/`bypassUpdate`.

Les fixtures négatives ne sont pas reportées à la campagne finale. Chaque bloc
d’implémentation reçoit immédiatement ses contrôles positifs et ses fixtures
négatives ciblées, avec diagnostic, site et obligation sémantique exacts. La
campagne finale vérifie ensuite la couverture exhaustive de l’ensemble sans
remplacer ces contrôles locaux.

## Critère binaire de réussite

La cible est atteinte si et seulement si toutes les obligations suivantes sont
fermées.

| Obligation | Verdict requis |
| --- | --- |
| C1–C17 corrigés | réussite complète |
| Transformation neuronale issue du run | démontrée génériquement |
| Oubli d’états préalablement distincts | exécuté et démontré |
| Méta-contrat fixe | tous les contrats et transitions opérationnels sont admis explicitement |
| Raccord constitutif RC1–RC6 | contrat opérationnel reçu, obligations indexées par l'état produit et contrat de futurs distingués ; témoins du même run, contraintes générales démontrées puis effectivement consommées, sans dépendance diagonale requise |
| Artefact sérialisé complet | programme, encodage, ports et décodeur raccordés |
| Base causale finie | déclarée, exécutable et couverte par la complétude relative |
| Vérificateur initial | exécutable et correct |
| Vérificateur de mise à jour | exécutable et correct |
| Complétude relative annoncée | démontrée |
| Runtime fermé aux mises à jour non certifiées | démontré par les types |
| Toute trace finie acceptée reste alignée | démontré |
| Tous les futurs couverts sont préservés | démontré |
| Identités stables entre versions | correspondance validée et transports démontrés |
| Cône causal constitutif complet | couvre réseau, décodage, action, mémoire et contrat |
| Certificats non affectés réutilisables | transportés sans rejouer l’histoire |
| `alignedUpdate` et `bypassUpdate` actuellement équivalents | démontré sur le domaine déclaré |
| `bypassUpdate` rejeté avant divergence | démontré par le runtime fermé |
| Artefact appris indépendant | protocole, provenance et empreinte vérifiés |
| Fixtures négatives exactes | toutes réussies |
| Comparaison de capacité | mêmes artefacts, mises à jour et propriétés comparés |
| Passage à l’échelle | protocole figé, reproduit et comparé au recheck complet |
| Anciennes preuves | aucune régression |
| Registre et passages FR/EN | frais et cohérents |
| Audit Lean complet | réussi |
| Audit indépendant de validité | verdict positif sur la révision exacte |
| Audit indépendant de portée et nouveauté | conclusion positive sur la capacité conjointe dans le corpus déclaré |

L’absence d’une seule obligation requise interdit le verdict « objectif
atteint ».

## Claim terminal visé

Le claim ne devra être enregistré qu’après achèvement de la cible. Sa
formulation candidate est :

> Pour tout méta-contrat fixé et toute trace finie de reconfigurations acceptée
> par le vérificateur constitutif, le runtime certifié n’effectue que des mises à
> jour et des actions dont la production conserve les contrats opérationnels
> admis à travers les occurrences neuronales, les autorisations, les effets, les
> successeurs et les oublis effectivement exécutés. Le contrôle incrémental
> transporte les certificats hors du cône causal constitutif affecté sans
> rejouer l’histoire et recalcule les autres. Sur un artefact appris indépendant,
> il accepte une mise à jour constitutivement alignée et rejette avant tout effet
> une mise à jour de contournement ayant le même comportement courant mais une
> provenance causale incompatible avec le contrat.

Ce claim devra inclure explicitement le raccord RC1–RC6 : sous les schémas
admis, les obligations sont instanciées sur les états des productions exécutées
et les contraintes observables sont certifiées depuis les témoins de ces mêmes
productions, indépendamment de la réalisation exacte candidate. Toute
réalisation exacte du contrat de futurs fixé doit respecter les contraintes
ainsi démontrées sur les sources raccordées. La fermeture de cette partie
requiert ses énoncés génériques, ses instances neuronales positives et ses
consommateurs dans le runtime, pas une nouvelle application de Gödel.

La priorité historique ou la qualification de percée ne fait pas partie du
théorème Lean. Elle exige la comparaison de capacité, un audit bibliographique
indépendant portant sur cette conjonction exacte de résultats et une conclusion
positive attachée à la révision scientifique auditée. Un rapport négatif ou
inconclusif ne ferme pas cette obligation.
