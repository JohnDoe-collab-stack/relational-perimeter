# Matrice de chantier — alignement neuronal constitutif

Statut : document temporaire de travail, à supprimer avant l’intégration dans
`main`.

Base : `1e5aeda745559d62a3819bb3213da7fce3c31ad1`.

La cible et les signatures autoritatives restent celles de la spécification
auditée. Cette matrice en suit les obligations sans en modifier la portée.

| Obligation | Construction positive | Consommation aval | Contrôle anti-substitution |
| --- | --- | --- | --- |
| T1, calcul natif | `executeWithTrace`, `NativeRun` | occurrences et rôles exécutés | une trace reconstruite indépendamment ne remplace pas la trace co-produite |
| T2, circuit constitué | `ReadsFrom`, `Reaches`, `reconstructCircuit` | rôle causal et explication | une arête décorative ou étrangère au run ne fournit pas le chemin indexé |
| T3, rôle causal | intervention locale sur le même run, changement propagé | `RequirementIncorporation` | activation seule et intervention directe sur la sortie sont insuffisantes |
| T4, exigence incorporée | `RequirementEncoding`, `RequirementIncorporation` | préservation du signal | un code constant ne reflète pas deux exigences reçues distinctes |
| T5, proposition alignée | chaque `ExecutedSignalTransformation` est construit depuis un `EffectiveReadsFrom`; la fonction locale et son exactitude sont dérivées du neurone exécuté et de son préfixe exact | élimination de `RequirementSignalPath`, puis `ActionRealization` | une fonction choisie après observation, une simple arête décorative ou une arête de poids nul ne remplace pas l’arête effectivement consommée |
| T6, sensibilité | deux exigences distinctes sur un même contexte | non-trivialité publique | les propositions produites sont distinctes |
| T7, action et effet | proposition produite, `executeProducedInput`, `EffectRealization` | état initial reconfiguré | commande, résultat et successeur indépendants sont interdits |
| T8, reconfiguration récursive | certificat indexé par le système et l’entrée de l’état courant | système cible, entrée et mémoire successeure du prochain état | un certificat du système initial ne certifie pas une queue reconfigurée |
| T9, continuation | `executeReconfiguredInteractions` récure sur l’état cible produit | étape suivante et état final | la tête ne lit pas le futur ; le système produit est consommé par la queue |
| T10, oubli exécuté, mémoire réduite et futurs non triviaux | `PublicHistoricalOperationalState` porte encore l’origine et le `ReconfiguredExecutionState` courant exact; `executeHistoricalForgetting` exécute au moins une étape causale depuis cet état riche et produit seulement la mémoire du terminal exécuté | contrat opérationnel d’agent avec admissions, refus, transitions et readout de table | ni une mémoire déjà réduite, ni une projection constante, ni l’état terminal complet, ni `PUnit` ne remplacent l’entrée historiquement renseignée et son exécution calculée |
| T11, composition | `ConstitutiveAlignmentCertificate` dans `Type` | certificat public `constitutive_alignment` | une proposition ou des témoins masqués par `Nonempty` ne remplacent pas la chaîne |

## Raccords désormais explicites

La chaîne finale n’est plus une conjonction de résultats indépendants.
`ConstitutiveAlignmentCertificate` contient, dans cet ordre :

1. l’incorporation dont le rôle est indexé par le run natif exact ;
2. la préservation de signal indexée par cette incorporation ;
3. l’action indexée par cette préservation ;
4. l’effet indexé par cette action ;
5. l’état reconfiguré dont la mémoire est le successeur de cet effet ;
6. l’histoire reconfigurée indexée par cet état et par chaque système cible
   produit récursivement ;
7. un programme d’oubli qui reçoit positivement deux états opérationnels
   distincts, portant chacun son origine historique et son état reconfiguré
   courant, puis exécute depuis chacun la chaîne complète ;
8. deux sorties calculées dont les preuves d’exécution les raccordent toutes
   deux à la mémoire de l’état final produit par cette histoire ;
9. une réalisation exacte qui omet le système et l’entrée du terminal tout en
   conservant, pour chaque continuation finie couverte, les autorisations,
   transitions, événements et readouts ;
10. l’impossibilité de récupérer les deux origines à partir de cette mémoire
    commune.

Le raccord T8 → T9 est porté par
`ReconfiguredActionEffect.targetState` : le système cible du certificat, la
nouvelle entrée et la mémoire effectivement produite deviennent ensemble
l’index de la queue. Le raccord T9 → T10 est porté par
`publicHistoricalForgettingProgram` : chaque entrée contient encore son origine
et un état reconfiguré courant ; les deux états courants sont eux-mêmes
distincts. L’exécution consomme cet état riche et commence obligatoirement par
la même exigence reçue avant de poursuivre la récursion reconfigurée jusqu’à la
mémoire terminale. Les équations
`leftOutputExact` et `rightOutputExact` relient ces sorties calculées à la
projection `ReconfiguredExecutionState.memory` du terminal de la continuation
certifiée. `reconfiguredOperationalMemoryRealization` prouve séparément que
cette projection préserve exactement tous les futurs couverts. L’égalité des
deux sorties est dérivée de leurs raccords au terminal ; elle n’est pas posée
par `rfl` lors de l’initialisation.

## Fermeture de C9 — mémoire strictement réduite

La sortie publique de l’oubli a désormais le type `Agent.Memory`, alors que
l’état source possède trois composantes : système natif courant, exigence
courante et mémoire. La réduction omet donc positivement les deux premières
composantes ainsi que l’origine historique, qui n’apparaît dans aucun de ces
types aval.

Le contrat réduit exécute chaque requête opérationnelle d’agent à partir de la
seule mémoire. La réalisation exacte fournit les deux transports
d’autorisation et leurs lois de retour, puis les égalités de transition,
d’événement et de lecture. Le théorème
`reconfiguredOperationalMemory_outcome_exact` en déduit l’égalité de chaque
résultat fini couvert.

## Fermeture de C10 — contrat de futurs non trivial

Le contrat terminal utilise `Agent.Admission`, et sa décision est calculée par
`ReachableAgent.decideAdmission` depuis l’exigence et le registre présents dans
la mémoire. Il n’utilise donc plus `PUnit`. Sur chaque mémoire terminale de
l’exécution publique, `publicTerminalAdmittedRequest` est effectivement admise
et `publicTerminalRefusedRequest` est effectivement refusée.

Le readout terminal est la table autorisée, non la mémoire complète. Les deux
mémoires `publicTerminalSeparatorLeft` et `publicTerminalSeparatorRight` ont le
même readout immédiat, mais la continuation non vide formée par
`publicTerminalSeparatingRequest` produit des décisions différentes. Le cas
vide ne suffit donc plus à capter toutes les distinctions du contrat.

La réalisation exacte entre l’état reconfiguré complet et la mémoire réduite
préserve les autorisations dans les deux sens, ainsi que chaque transition,
événement, readout et résultat fini. La fixture
`TrivialAuthorizationCannotReplaceTerminalContract.lean.fail` interdit de
réintroduire une autorisation terminale uniforme par `PUnit`.

## Fermeture de C11 — préservation proposition–action

`AgentActionChannel` n’est plus une simple fonction de la proposition vers une
requête. Chaque canal déclare maintenant une relation de distinction
propositionnelle requise, une relation de collision permise, une preuve que
toute distinction requise produit deux requêtes distinctes et une
caractérisation exacte de toutes les collisions de commandes permises.

L’instance publique exige la distinction de `false` et `true`, et la transporte
jusqu’aux requêtes exécutées `.advance 0` et `.advance 1`. Ses collisions ne
sont autorisées que lorsque les propositions sont égales. Les théorèmes
`public_actions_preserve_required_proposal_distinction` et
`public_action_collisions_are_exactly_permitted` raccordent ce contrat aux
requêtes effectivement contenues dans `publicAction`, plutôt qu’à une fonction
de commande isolée.

La fixture
`CollapsingCommandCannotPreserveRequiredDistinction.lean.fail` vérifie qu’une
commande constante ne peut pas remplacer la commande publique tout en
conservant son contrat de distinction. Ainsi, aucune distinction exigée par le
contrat public ne peut disparaître silencieusement entre proposition produite
et action exécutée.

## Fermeture de C12 — instance publique substantielle

`publicSubstantiveAlignment` est une instance publique unique de la chaîne
complète, et non un inventaire de petits exemples sans raccord. Son certificat
`PublicSubstantiveInstanceCertificate`, réalisé par
`publicSubstantiveInstance`, ferme ensemble les obligations suivantes :

- les exigences `.scopeZero` et `.scopeOne` et les contextes `.direct` et `.reversed`
  sont effectivement distincts ;
- les propositions exigées varient avec le couple exigence–contexte ;
- le système reconfiguré possède deux sorties produites et la transformation du
  signal n’est pas l’identité ;
- l’action préserve la distinction propositionnelle requise ;
- changer séparément l’état source, l’exigence suivante ou son contexte change
  la sortie du système reconfiguré ;
- l’autorisation est lue exactement au port que le transport constitutif lui
  assigne ;
- la continuation publique consomme deux requêtes produites ;
- l’oubli reçoit deux états opérationnels distincts qui portent encore leurs
  origines, s’exécute jusqu’à la mémoire terminale et rend impossible la
  reconstruction simultanée de ces deux origines ;
- le contrat terminal admet une requête et en refuse une autre sur cette même
  mémoire produite.

Les théorèmes `substantive_instance_*` du test de régression exposent chaque
obligation du certificat sur l’instance elle-même. La fermeture de C12 ne repose
donc ni sur une simple copie binaire, ni sur une liste de propriétés prises dans
des instances différentes : les différences d’entrée, la transformation, la
reconfiguration, l’autorisation, la continuation, l’oubli et le contrat de futurs
sont tous raccordés à la même chaîne publique.

## Fermeture de C13 — vocabulaire exact

Les anciens constructeurs publics `deny` et `allow` ont été supprimés. Ils
nommaient des cas d’exigence avant toute décision du contrat et suggéraient donc
respectivement un refus et une admission qui n’étaient pas portés par leur type.

Les constructeurs `scopeZero` et `scopeOne` décrivent maintenant uniquement la
donnée effectivement reçue : les théorèmes `public_scope_zero_scope_exact` et
`public_scope_one_scope_exact` prouvent que leurs scopes valent exactement `[0]`
et `[1]`. Les contextes `direct` et `reversed` décrivent leur opération réelle sur
la proposition : les théorèmes `public_direct_proposals_exact` et
`public_reversed_proposals_exact` fixent la table complète des quatre cas.

Le vocabulaire d’admission et de refus est conservé uniquement au niveau où le
contrat terminal calcule effectivement ces décisions :
`publicTerminalAdmittedRequest` est activée par
`public_terminal_admitted_request_enabled`, tandis que
`publicTerminalRefusedRequest` est désactivée par
`public_terminal_refused_request_disabled`. Les régressions
`public_case_names_match_received_scopes` et
`public_context_names_match_proposal_table` rendent cette correspondance entre
noms publics et comportements formels directement vérifiable.

## Fermeture de C14 — fixtures négatives sémantiquement ciblées

Le registre `scripts/expected-failures.tsv` fixe désormais, pour chaque fixture,
six données obligatoires : fichier, catégorie, ligne, colonne, fragment exact du
diagnostic JSON de Lean et obligation sémantique effectivement testée. Le
vérificateur refuse une obligation absente ou marquée comme placeholder, une
erreur supplémentaire, un autre site, une autre classe d’erreur ou une fixture
qui compilerait.

La fixture `ForeignCertificateCannotReplaceCanonicalCertifier.lean.fail`
n’échoue plus sur la confusion préalable entre une action et une étape causale.
Tous ses arguments et la queue dépendante sont correctement formés. Son unique
erreur est maintenant l’obligation exacte
`foreign = certify source next` : Lean refuse que `rfl` identifie le certificat
étranger au certificat canonique produit pour la source et l’entrée suivantes.
Une fois cette égalité disponible, la substitution rend la construction de
l’étape canonique et de sa queue bien typée ; l’échec porte donc sur la
propriété scientifique annoncée, pas sur une arité ou un argument manquant.
Le contrôle positif générique `canonicalCertificateBuildsHead` compile avec la
même construction lorsque le certificat fourni est exactement celui de
`certify`.

Les tests du vérificateur couvrent aussi l’absence de l’obligation sémantique
dans le registre. Le passage de l’ensemble des fixtures exige ainsi à la fois
leur refus par Lean et l’identité exacte de la raison enregistrée.

## Fermeture de C15 — décomposition exacte du résultat scientifique

`ConstitutiveScientificDecomposition` est une vue générique du certificat
terminal. Elle n’ajoute aucune hypothèse :
`decomposeConstitutiveAlignment` construit chacun de ses champs en éliminant le
même `ConstitutiveAlignmentCertificate`. Les statuts scientifiques ne sont donc
plus laissés au seul commentaire : leurs types et leurs noms les séparent.

| Statut | Donnée ou résultat exact |
| --- | --- |
| reçu comme contrat | canal d’action, constructeur de reconfiguration, certificateur, programme d’oubli et contrat de futurs, chacun accompagné de son égalité au paramètre reçu |
| produit par exécution | rôle causal interventionnel du run exact, transformation locale dérivée du neurone et de l’arête effective, résultat d’action, effet, continuation et deux sorties du programme d’oubli, avec leurs équations d’exécution |
| dérivé | proposition initiale, requête initiale et proposition de la première reconfiguration, obtenues par élimination des témoins de transformation et de dérivation |
| seulement autorisé | permission incorporée de la première reconfiguration, identifiée à celle du certificat exact sans être présentée comme une exécution |
| conservé | équivalence de tous les futurs couverts par le contrat reçu |
| oublié | origines présentes dans deux états opérationnels initialement distincts, puis absentes de la sortie réduite commune produite par les deux exécutions |
| rendu irrécupérable | impossibilité, pour toute fonction depuis la sortie réduite, de reconstruire simultanément les deux origines distinctes |

Les cinq confusions interdites sont fermées explicitement :

- le champ causal produit a le type `CausalRole`, et non `Reaches` ;
- `derivedInitialProposal` vient de `proposal_aligned` et
  `derivedHeadProposal` de `ReconfiguredCausalStage.proposal_required_exact` ;
  aucune égalité finale de proposition n’est reçue comme champ ;
- les sorties oubliées portent chacune
  `ExecutedHistoricalForgetting.executionExact`, tandis que la fixture
  `ConstantProjectionCannotWitnessExecutedForgetting.lean.fail` interdit de
  substituer une projection constante indépendante ;
- `AlreadyForgottenInputCannotWitnessExecutedForgetting.lean.fail` et
  `ReducedMemoryCannotReplaceHistoricalOperationalState.lean.fail` interdisent
  de commencer l’oubli depuis une mémoire qui ne porte déjà plus l’origine ;
- `PostHocConstantTransformCannotWitnessExecution.lean.fail` et
  `PostHocTransformCannotReplaceExecutedEdge.lean.fail` interdisent qu’une
  fonction choisie après observation et un simple `ReadsFrom` remplacent
  l’arête effective dont l’action neuronale détermine la transformation ;
- la sortie publique réduite est `Agent.Memory`, distincte du
  `ReconfiguredExecutionState` complet ; la fixture
  `CompleteStateCannotReplaceReducedMemory.lean.fail` impose cette frontière ;
- `publicConstitutiveScientificDecomposition` est l’application de la
  décomposition générique au certificat public, et non une généralité inférée
  depuis l’instance.

Les régressions `scientific_*` exposent séparément les sept statuts sur la même
chaîne publique et leurs audits axiomatiques sont vides.

## Fermeture de C16 — absence de régression

La non-régression de la chaîne neurale est désormais exposée par des
déclarations dédiées, et non déduite du seul succès de la construction. Les
projections `ReconfiguredInteractionHistory.headStage` et
`ReconfiguredInteractionHistory.tail` rendent accessible le véritable premier
témoin stocké par une histoire non vide puis sa véritable queue. Le type de la
queue mentionne directement `history.headStage.nextState` : la continuation
consomme donc le successeur produit par ce même témoin, et non un état reconstruit
séparément.

| Obligation de C16 | Gate positive exacte |
| --- | --- |
| production et consommation du même témoin | `c16_same_witness_is_produced_and_consumed` assemble une chaîne Sigma dont chaque composant est indexé par le précédent |
| occurrence exacte du run | `c16_exact_proposal_occurrence` porte exactement le système public et `scopeZeroDirectInput` dans son type |
| distinction entre valeur et occurrence | `c16_occurrence_value_is_separate_readout` projette la valeur depuis l’occurrence sans les identifier |
| action réellement exécutée | `c16_action_is_the_actual_execution` identifie le résultat de l’action à l’appel exact de `Agent.executeInput` |
| effet réellement produit | `c16_effect_is_the_produced_execution_result` identifie le couple successeur-événement au résultat exécuté |
| transmission du successeur produit | `c16_produced_successor_is_transmitted` relie la mémoire de l’état initial reconfiguré au successeur exact de l’effet |
| dépendance de chaque reconfiguration au système produit précédent | `c16_actual_tail_consumes_produced_state` et `c16_second_reconfiguration_consumes_previous_production` extraient la vraie queue et sa vraie tête sous l’indice `completePublicChain.continuation.headStage.nextState` |

La non-régression des résultats antérieurs est contrôlée séparément depuis le
socle `1e5aeda745559d62a3819bb3213da7fce3c31ad1`. Le diff des quatre fichiers
fondationnels, des arbres `Constitution/Godel`, `Constitution/Tarski`,
`Instances/HeytingArithmetic` et `Computation`, ainsi que de leurs régressions
Gödel, Tarski, regroupement et runtime, est vide. Ces sources restent donc
octet pour octet celles du socle. La construction globale recompile en outre
leurs modules et leurs tests dans le même graphe que les nouveaux résultats ;
l’audit exhaustif des constantes interdit qu’une dépendance axiomatique
manuscrite soit apparue ailleurs. Aucun énoncé antérieur n’a été supprimé,
affaibli ou remplacé pour fermer C16.

## État de C17 — validation Lean complète

Les contrôles de C17 ont été exécutés sur l’arbre de travail complet, sans
omettre les tests ni limiter le balayage aux nouveaux modules :

- `lake build` réussit en 401 tâches, sans avertissement ;
- l’audit exhaustif couvre 33 175 constantes issues de 398 modules et rapporte
  zéro déclaration manuscrite dépendante d’un axiome ;
- les 399 fichiers Lean suivis ou nouveaux possèdent exactement un bloc
  `AXIOM_AUDIT` final et un artefact `.olean` produit par la construction ;
- aucun de ces fichiers ne contient `axiom`, `unsafe`, `noncomputable`,
  `Classical`, `propext`, `Quot.sound`, `native_decide`, `implemented_by`,
  `sorry` ou `admit`, ni une dépendance de migration interdite ;
- les fixtures positives sont toutes élaborées par la construction globale ;
- les 86 fixtures négatives sont toutes refusées par leur unique diagnostic
  Lean, au site et pour l’obligation sémantique enregistrés ;
- les auto-tests du parseur d’imports passent, ainsi que les dix-huit
  inventaires de frontières constitutives ;
- l’auto-test de stratification passe et les 332 modules de production sont
  inventoriés, contraints et dépourvus d’orphelin ;
- les cinq contrôles de code généré — instance unifiée, agent, signatures de
  continuation, maître variable et machine intégrée — passent ; ils vérifient
  les appels réellement compilés et interdisent les reconstructions ou
  énumérations substitutives prévues par leurs contrats ;
- les 189 déclarations publiques et 64 déclarations de test déjà enregistrées
  dans le registre scientifique se résolvent encore en Lean et leurs audits
  axiomatiques sont vides ;
- les 45 documents Markdown suivis ou nouveaux ont des liens locaux valides ;
- `git diff --check` passe, aucun fichier n’est supprimé depuis le socle C16 et
  les sources historiques protégées restent identiques.

Le socle corrigé a été figé au commit
`13f9e0977fcd79ae47504fc32400a90a3b17eeb1`. Les quatre claims dont la fermeture
d’import consomme le registre des fixtures ont reçu une nouvelle révision
probatoire sur ce SHA et une empreinte recalculée depuis ses sources. Les deux
portails officiels, `scripts/verify.ps1` sous PowerShell et `scripts/verify.sh`
sous Git Bash, ont ensuite été exécutés intégralement sur le même état : ils
terminent tous deux avec succès et contrôlent les mêmes 399 fichiers Lean.
C17 est donc fermé sur ce socle scientifique stable.

## Stratification imposée

Les modules mécanistiques et neuronaux occupent des strates machine strictes :

```text
M0 Arithmetic
→ M1 Program
→ M2 Execution
→ M3 Occurrence
→ M4 Relations
→ M5 Circuit
→ M6 Intervention
→ M7 Explanation
→ M8 RequirementEncoding
→ M9 ProposalAlignment
→ M10 RequirementSensitivity / ActionRealization
→ M11 PublicRequirementAlignment / InteractionHistory
→ M12 Reconfiguration
→ M13 ReconfiguredContinuation
→ M14 ExactForgetting / ReconfiguredExactForgetting
→ M15 PublicActionRealization
→ M16 PublicExactForgetting
→ M17 ConstitutiveAlignment
→ M18 OperationalContract
→ M19 SerializedNativeSystem
→ M20 StableNodeIdentity
→ M21 FiniteCausalBasis
→ M22 CoveredFutureRealization
→ M23 StateConstitutiveCertificate
→ M24 CheckedState
→ M25 ReferenceChecker
→ M26 StableNodeCorrespondence
→ M27 HeterogeneousCausalGraph
→ M28 AffectedConstitutiveCone
→ M29 LocalCertificateReuse
→ M30 IncrementalChecker
→ M31 IncrementalReferenceEquivalence
→ M32 CheckedUpdateTrace
→ M33 CertifiedRuntime
→ M34 CertifiedRuntimeAccessibility
→ M35 IndependentLearnedArtifact
→ M36 LearnedUpdateSeparation
→ M37 FiniteCounterfactualDivergence
→ M38 public root
```

La gate refuse toute dépendance vers une strate machine égale ou supérieure.
Les modules ne sont donc plus rassemblés dans une strate `U` incapable
d’imposer leur ordre constitutif interne.

## Contrôles ajoutés

Les régressions positives vérifient que l’effet produit initialise l’état, que
la continuation exécute exactement ses requêtes produites, que les deux entrées
historiques restent distinctes, que leurs deux exécutions d’oubli calculent le
terminal produit par la continuation, et que la sortie commune préserve tous
les futurs reconfigurés couverts.

Les fixtures négatives vérifient notamment que :

- le certificat du système public initial ne certifie pas un état arbitraire ;
- le contrat futur de l’ancien système fixe ne remplace pas le contrat
  reconfiguré ;
- `True` ne remplace pas le certificat dépendant final ;
- la mémoire antérieure à l’action ne remplace pas son successeur produit ;
- l’état initial ne remplace pas l’état final produit à l’entrée de l’oubli ;
- un certificat construit séparément ne remplace pas le résultat du
  certificateur canonique de l’étape ;
- un programme constant retournant un état fourni ne remplace pas le programme
  d’oubli historique indexé par le certificat final ;
- une mémoire déjà réduite ne remplace pas l’état opérationnel qui porte encore
  l’origine à l’entrée de l’exécution d’oubli ;
- une fonction arbitraire accompagnée d’un simple `ReadsFrom` ne remplace pas
  la transformation dérivée de l’arête neuronale effective ;
- l’état terminal complet ne peut pas être utilisé là où la sortie réduite
  exige uniquement `Agent.Memory`.

## État actuel des vérifications

- construction ciblée de tous les nouveaux modules : réussie ;
- tests positifs neuronaux : réussis après adaptation à l’interface dépendante ;
- 101 fixtures négatives : toutes rejetées au diagnostic et au site
  enregistrés, dont la construction directe interdite du résultat incrémental ;
- inventaire de stratification : 346 modules, tous contrôlés, aucun orphelin ;
- tous les nouveaux audits `#print axioms` : aucun axiome ;
- construction globale : réussie, 422 tâches, audit exhaustif de 35 368
  constantes sur 419 modules, aucune déclaration manuscrite dépendante d’un
  axiome ;
- gates locales de ce bloc : stratification et fixtures négatives réussies ;
- registre scientifique : son renouvellement exige une révision Git stable et
  reste donc volontairement différé tant que ce chantier n’est pas commité ;
  aucun succès global des portails n’est revendiqué avant ce renouvellement.

## Extension incrémentale — méta-contrat opérationnel

Le module `OperationalContract` ajoute un méta-contrat fixé avant l’exécution.
Il sépare explicitement les sept composantes exigées du contrat opérationnel :
encodage, causalité, préservation proposition–action, admission de
l’autorisation, satisfaction par l’effet, futurs couverts et politique
historique. Les admissions et les permissions de transition appartiennent au
méta-contrat ; le constructeur de transition ne reçoit ni fonction de
transport ni procédure de revérification choisie par le client.

La réalisation publique autorise uniquement le passage du contrat initial au
contrat reconfiguré. Ces deux contrats ne sont pas deux noms pour la même
valeur : leur obligation historique change de domaine. Le contrat initial
porte l’état historique complet, tandis que le contrat reconfiguré exige un
témoin indexé par l’état effectivement produit par une reconfiguration. La
distinction d’action est transportée par la règle du méta-contrat et
l’autorisation incorporée est reconstruite par sa règle de revérification.
La transition inverse est refusée par une fixture au site exact.

## Extension incrémentale — artefact neuronal sérialisé

Le module `SerializedNativeSystem` introduit une représentation de données
autonome pour les sources, arêtes pondérées, neurones et ports de sortie. Le
décodeur exécutable contrôle l’arité d’entrée, chaque indice d’entrée, la
chronologie de chaque référence à un neurone antérieur, chaque port de sortie
et la non-vacuité des sorties avant de construire un `NativeSystem` complet.

Le contrat fixé fournit l’encodeur d’exigence et le décodeur de proposition ;
l’artefact fournit le programme et les ports. `ArtifactDecodingExact` raccorde
le système retourné aux quatre données constitutives : arité, programme
sérialisé — poids compris —, ports sérialisés, encodeur et décodeur du contrat.
Le constructeur du résultat décodé est privé. Les fixtures négatives montrent
qu’après décodage ni poids, ni ports, ni décodeur ne peuvent être remplacés en
réutilisant le certificat exact.

Les contrôles positifs couvrent en outre séparément les cinq refus du
décodeur : arité incompatible, entrée inexistante, référence future, sortie
inexistante et liste de sorties vide. Les deux modules sont accessibles depuis
la racine publique, occupent les strates `M18` et `M19`, et tous leurs audits
axiomatiques sont vides. Cette extension ferme uniquement les deux blocs
annoncés ; elle ne prétend pas encore fermer le vérificateur initial ou le
vérificateur de mise à jour de la cible terminale.

## Extension incrémentale — domaine décidable et base causale finie

Le contrat opérationnel déclare désormais explicitement sa liste finie
d’entrées courantes et son alphabet fini de remplacements. `FiniteCausalBasis`
reste indexée par ce contrat et par l’artefact exactement décodé. Sa couverture
ne porte donc pas sur des entiers arbitraires : pour chaque entrée déclarée,
elle fournit positivement un identifiant du système décodé, le `CausalRole`
exécuté à cette occurrence et l’appartenance du remplacement à la fois à la
liste locale du nœud et à l’alphabet du contrat.

Les décisions d’égalité et d’appartenance sont exécutables et constructives.
La réalisation publique couvre les quatre couples exigence-contexte et les
remplacements effectivement employés par leurs interventions causales. Une
base vide d’entrées ou de remplacements ne peut pas réutiliser ces preuves de
couverture.

## Extension incrémentale — réalisation exacte de tous les futurs

Le contrat opérationnel porte maintenant son véritable `FutureContract`.
`FutureContractSimulationData` isole les sept lois locales de transport puis
les assemble dans l’API `ExactRealization` déjà présente. Le théorème générique
de conservation est obtenu par `ExactRealization.outcome_exact` et quantifie
sur toute liste finie de requêtes ; aucun ensemble d’exemples ne le remplace.

La réalisation publique réemploie le contrat terminal, la projection mémoire
et l’`ExactRealization` déjà établis par l’oubli exact. Elle n’introduit donc ni
une seconde sémantique des futurs ni une projection indépendante. Une fixture
négative empêche de réutiliser ces lois avec un contrat réduit dont le readout
a été prescrit séparément.

## Extension incrémentale — certificat constitutif d’état

`StateConstitutiveCertificate` est indexé simultanément par le contrat
opérationnel fixé, l’artefact exactement décodé et l’état d’exécution exact. Il
consomme la base causale finie, l’appartenance positive de l’entrée au domaine
déclaré, les sept familles d’obligations du contrat et la réalisation exacte de
ses futurs. Le système de l’état est identifié au système de l’artefact dans le
type du certificat. Le candidat causal attaché à l’entrée et la conservation de
tout futur fini sont ensuite des projections de cette même chaîne, non des
reconstructions indépendantes.

## Extension incrémentale — agents et mises à jour vérifiés

Les constructeurs de `CheckedAgent` et `CheckedUpdate` sont privés. Un agent
vérifié porte l’admission du membre exact du méta-contrat, son artefact décodé,
son état et le certificat indexé par ces deux derniers objets. Une mise à jour
vérifiée porte comme successeur un nouvel agent déjà certifié, la permission de
transition du même méta-contrat et un témoin d’exécution indexé par les états
source et cible exacts. Le méta-contrat public définit ce témoin par l’action de
reconfiguration réellement exécutée ; une paire d’états sans cette production
ne constitue donc pas une mise à jour vérifiée.

Ce bloc ferme les types certifiés et une instance initiale publique.

## Extension incrémentale — vérification initiale et recheck complet

`checkInitial` décode entièrement le réseau sérialisé avant d’accepter
l’artefact initial de référence. Un artefact mal formé reçoit le diagnostic du
décodeur ; un artefact bien formé mais différent ne peut pas recevoir le
certificat de référence. Son théorème de correction identifie tout résultat
positif à l’agent vérifié exact.

Le contrat reconfiguré décrit désormais le système effectivement produit :
ses obligations sont indexées par l’état exact et consomment séparément
l’encodage, le rôle causal, l’action, l’autorisation et l’effet portés par la
même production. Sa base causale est attachée à l’artefact cible complètement
décodé, et sa politique de futurs exécute la continuation depuis ce même état.

`checkReferenceUpdate` est le vérificateur complet de référence, distinct du
futur vérificateur incrémental. Son entrée contient seulement le réseau cible
complet et l’exigence suivante, jamais un certificat. Il redécode le programme
entier, contrôle l’artefact et le successeur exacts, puis retourne le
`CheckedUpdate` dont l’état cible est celui produit par la reconfiguration. La
correction identifie tout succès à cette mise à jour exacte ; la complétude est
limitée aux deux conditions locales décidables effectivement contrôlées.

## Extension incrémentale — identités stables entre versions

`StableNodeKey` est désormais distinct de tout indice `Fin`. Chaque artefact
décodé reçoit un `StableArtifactNaming` injectif pour ses entrées reçues, ses
neurones et ses ports de sortie. Une occurrence locale conserve donc sa
position d’exécution, mais cette position n’est plus prise pour son identité.

`ValidatedStableNodeCorrespondence` est une correspondance partielle entre deux
versions. Un transport réussi produit simultanément la nouvelle occurrence et
la preuve que sa clé stable est inchangée. Les suppressions et insertions
restent représentées par l’absence d’image ou d’antécédent. Dans l’instance
publique, l’entrée d’exigence est réindexée de la position zéro à la position
un tout en conservant sa clé ; l’entrée d’autorisation insérée n’a aucun
antécédent dans l’ancien artefact.

## Extension incrémentale — graphe causal constitutif hétérogène

`ConstitutiveDependency` relie sans les confondre les occurrences neuronales,
les ports de sortie, le décodeur, la proposition, l’action, l’effet, l’état
successeur, la projection mémoire et les sept observations du contrat. Ce
graphe est une relation indexée par le `StateConstitutiveCertificate` exact,
pas une liste d’arêtes fournie indépendamment.

L’arête neuronale initiale est le rôle causal exécuté sélectionné par la base
finie certifiée. Les arêtes suivantes consomment respectivement les ports du
système décodé et les témoins distincts d’interprétation de l’action,
d’effectuation, d’histoire, d’autorisation et de futur du même certificat.
Chaque nœud du graphe possède en outre une clé stable ; son transport entre
versions passe par la correspondance validée et transporte positivement
l’égalité de cette clé.

## Extension incrémentale — cône affecté calculé

`affectedConstitutiveNode` calcule le cône depuis la modification réellement
validée. Les insertions, suppressions et observations structurelles modifiées
amorcent le calcul ; sa fermeture suit les lectures neuronales de poids non
nul puis la chaîne hétérogène allant du port de sortie aux observations du
contrat. Les observations du nouveau contrat sont invalidées à la frontière
de version au lieu d’être déclarées réutilisables sans transport.

Dans l’instance publique, l’entrée d’autorisation insérée, le neurone de
proposition et l’action en aval appartiennent au cône. L’entrée d’exigence
réindexée en est exclue : sa correspondance est validée et son observation
structurelle est identique dans les deux certificats. Le théorème générique
`outsideAffectedCone_unchanged` dérive alors l’égalité des observations de
l’absence calculée dans le cône ; il ne reçoit pas cette égalité comme
hypothèse.

## Extension incrémentale — réutilisation locale transportée

`LocalCertificateFragment` contient le fragment ancien et son équation
d’observation dans le certificat source. `Unaffected` exige simultanément le
transport positif de son nœud par la correspondance validée et son exclusion
du cône calculé. `transportCertificateFragment` consomme ces deux résultats et
place exactement l’ancien payload sous la même clé stable dans le certificat
cible. Le payload n’est ni recalculé ni remplacé par une observation cible.

L’instance publique transporte ainsi le fragment de l’entrée d’exigence de sa
position ancienne à sa position nouvelle. Une fixture négative interdit de
déclarer réutilisable le neurone de proposition, dont l’appartenance au cône
est calculée à `true`.

## Extension incrémentale — vérificateur de delta

`IncrementalNeuralUpdate` contient uniquement une liste d’éditions sérialisées
et l’entrée suivante. Il ne peut transporter ni certificat, ni correspondance
stable, ni décision sur le cône affecté. `checkIncrementalUpdate` applique ces
éditions à la source certifiée, contrôle le réseau cible matérialisé et
l’entrée suivante, puis retourne un paquet dont le constructeur est privé.

Ce paquet conserve séparément le fragment ancien réellement transporté et les
observations recalculées dans le cône affecté. Il expose leurs listes et leurs
comptes distincts, ainsi que l’égalité de leur assemblage avec l’observation
structurelle du certificat cible. Le vérificateur incrémental ne redécode pas
l’artefact complet et n’appelle pas le vérificateur complet de référence.

## Extension incrémentale — équivalence avec le recheck complet

L’équivalence est constructive et vaut pour tout delta sérialisé : le
vérificateur incrémental accepte exactement lorsque le vérificateur complet
accepte le réseau matérialisé et la même entrée suivante. La preuve passe par
les deux conditions locales réellement décidées par les programmes ; elle ne
réécrit pas une proposition par extensionalité.

Lors d’un succès, le résultat incrémental et le résultat du recheck complet
sont identifiés comme le même `CheckedUpdate`. Sur le delta public, l’égalité
porte directement sur les deux valeurs exécutables de type `Except`, après
effacement du supplément incrémental. Cette égalité certifie le résultat, pas
une borne asymptotique sur son coût.

## Extension incrémentale — trace finie dépendante vérifiée

`CheckedReconfigurationTrace` indexe une histoire finie par son agent vérifié
source, sa liste exacte de deltas et son agent vérifié final. Chaque
constructeur de pas conserve le résultat positif exact de
`checkIncrementalUpdate`; la queue commence obligatoirement sur
`incremental.checked.next`. `EveryCheckedStepSatisfies` reconstruit alors, pas
par pas, l’identification de chaque résultat stocké avec la mise à jour
certifiée produite par le vérificateur.

Le méta-contrat public actuel autorise uniquement la transition de `initial`
vers `reconfigured`. `checkUpdates` accepte donc la trace vide ou un unique pas
vérifié et refuse explicitement une seconde mise à jour avec
`noAdmittedTransition`. La trace est récursive et dépendante ; le cas public ne
lui ajoute pas une transition réflexive qui n’existe pas dans le contrat.

## Extension incrémentale — API runtime fermée

`CertifiedRuntime` possède un constructeur privé. Il conserve ensemble la
liste des deltas acceptés, l’agent courant, la trace dépendante exacte qui y
conduit et la preuve constructive de tous ses pas. `submitUpdate` est l’unique
opération publique de reconfiguration : il appelle `checkIncrementalUpdate`
et installe exactement `incremental.checked.next`, jamais un successeur fourni
ou reconstruit séparément.

Après le premier pas autorisé, l’historique scellé fait refuser toute nouvelle
soumission, conformément au méta-contrat actuel. Les constructeurs du résultat
de trace et du runtime sont privés et font l’objet de fixtures négatives ; les
régressions positives vérifient l’acceptation du delta public, son résultat
exact et le refus de la continuation non autorisée.

## Extension incrémentale — accessibilité de tous les états du runtime

`CertifiedRuntimeReachable` est la plus petite famille engendrée par
`initialCertifiedRuntime` et par les égalités attestant un succès effectif de
`submitUpdate`. Une simple valeur de type `CertifiedRuntime` ne peut donc pas
être déclarée atteignable sans exhiber toute sa chaîne d’accès par l’API.

`reachableRuntime_accessibility` associe à chaque état atteignable une
`CertifiedRuntimeAccessibility` contenant sa trace dépendante exacte et la
preuve constructive de tous ses pas. Les indices de cette trace sont
directement `runtime.updates` et `runtime.current` : ni l’historique ni l’agent
final ne sont reconstruits séparément. Dans l’instance publique, l’état initial
et l’état reconfiguré sont accessibles ; aucun successeur de ce dernier ne
peut être produit, puisque le méta-contrat n’autorise pas une seconde
transition.

## Extension incrémentale — protocole comparatif et artefact appris

Le protocole comparatif `constitutive-neural-alignment-comparison-v1` est figé
avant toute expérience confirmatoire. Il fixe six classes de baselines, leur
interface sur le même artefact et la même trace, ainsi que les huit capacités
qui devront être rapportées séparément. Les adaptateurs encore absents sont
explicitement marqués comme tels : leur absence ne vaut ni résultat négatif ni
impossibilité universelle.

L’artefact indépendant est produit par une recherche exhaustive déterministe
sur les huit combinaisons d’exigence, de contexte et d’autorisation. Son graphe
multicouche expose trois observations distinctes : sortie autorisée,
autorisation et chemin de contournement. Deux transformations successives
étendent ensuite effectivement ce graphe. Aucun poids n’est choisi dans une
preuve Lean ni retouché après apprentissage.

Le manifeste enregistre la commande, les paramètres, la provenance, les
conditions de réemploi et les empreintes SHA-256. La gate reproduit dans un
répertoire temporaire l’artefact JSON, sa traduction Lean et le manifeste,
puis exige une identité octet par octet. Le module Lean généré est décodé par
le décodeur public pour chacune des trois versions, sans axiome. Ce bloc ne
publie aucune mesure confirmatoire : le protocole a été figé avant la
construction des mises à jour `alignedUpdate` et `bypassUpdate`.

## Extension incrémentale — séparation alignée et contournement

`checkIndependentLearnedInitial` décode d’abord l’artefact appris initial et
produit l’unique état initial certifié consommé ensuite par les deux chemins.
`alignedUpdate` et `bypassUpdate` partent de cet état commun et portent
exactement la même intention admise. Sur les quatre cas du domaine
courant déclaré, leurs sorties sont identiques. Tout vérificateur extensionnel
qui factorise uniquement par cette table finie donne donc la même réponse pour
les deux candidats.

La différence est constitutive et calculée sur les artefacts sérialisés.
`primaryAuthorizationConstitutivelyConsumed` exige à la fois un chemin de poids
non nul depuis l’entrée d’autorisation reçue jusqu’à la sortie principale et
une variation effective de cette sortie entre deux entrées séparatrices qui ne
diffèrent que par l’autorisation. La mise à jour alignée satisfait ces deux
conditions. La mise à jour de contournement conserve le comportement courant
mais fait produire la sortie principale par une observation qui ne dépend pas
de l’autorisation.

`checkIndependentLearnedUpdate` reconstruit ces faits depuis le candidat et
l’état initial certifié : il contrôle leur raccord source, l’intention admise,
le décodage certifié et la consommation effective de l’autorisation. Il accepte `alignedUpdate` et
rejette `bypassUpdate` avec `missingConstitutiveDependency`. L’installation est
strictement en aval de ce résultat ; le contournement est donc refusé avant
tout effet.

## Extension incrémentale — divergence contrefactuelle finie

Le témoin futur est explicite et non vide. Pour la requête où l’exigence est
vraie, le contexte faux et l’autorisation fausse, la simulation totale de
`alignedUpdate` produit exactement `[0, 0, 1]`, tandis que celle de
`bypassUpdate` produit `[1, 0, 1]`. La première satisfait le contrat futur ; la
seconde le viole.

`ConstitutiveLatentBypassCertificate` rassemble sans substitution la même
intention admise, l’équivalence sur tout le domaine courant déclaré, l’accord
de tous les vérificateurs extensionnels ainsi factorisés, l’acceptation de la
mise à jour alignée, le rejet du contournement, la divergence future calculée
et le refus avant effet. Il établit donc un contournement latent concret :
invisible dans le comportement courant déclaré, mais séparé par la dépendance
constitutive et exposé par un futur fini exécuté.

## Campagne finale de mutations négatives

La campagne figée `constitutive-neural-final-negative-mutations-v2` couvre les
huit substitutions terminales exigées : suppression de la dépendance à
l’autorisation, substitutions séparées du contexte et de l’exigence,
court-circuit du système antérieur, transformateur constant postérieur,
arête de poids nul, histoire déjà effacée et reconstruction indépendante du
successeur. Chaque cas est raccordé à une fixture Lean déjà locale ou ajoutée
au raccord concerné. La gate commune exige l’échec à la classe de diagnostic,
à la ligne et à la colonne enregistrées ; un autre échec ne valide pas la
mutation. Le manifeste final vérifie que les huit obligations sont présentes
une fois chacune dans cet inventaire exécutable.

## Passage à l’échelle et comparaison avec le recheck complet

Le protocole confirmatoire `constitutive-neural-incremental-scaling-v2` fixe
avant le run une famille de chaînes neuronales chronologiques non nulles de
100, 1 000, 5 000, 20 000 et 50 000 neurones. Il ne recopie pas une instance
fixe : chaque taille ajoute des neurones et des dépendances causales au graphe.
Le même suffixe terminal de quatre neurones est modifié à chaque taille.

Les deux chemins vérifient exactement la même propriété du même artefact cible :
la bonne formation de toutes ses références chronologiques et de son port de
sortie. Le recheck complet repart de zéro. Le recheck incrémental consomme le
certificat initial, contrôle l’identité de chaque fragment de préfixe déclaré
réutilisé et recalcule tout le suffixe affecté. Les résultats coïncident aux
cinq tailles. Le comptage déterministe passe respectivement de 202 à 107 unités
à 100 neurones, puis de 100 002 à 50 007 unités à 50 000 neurones ; les quatre
fragments affectés sont recalculés et tous les autres sont enregistrés comme
réutilisés. Les médianes temporelles observées sont conservées séparément et
ne sont ni un théorème Lean ni une revendication générale de complexité.

Le protocole, le générateur, les paramètres, la commande, les résultats et la
campagne de mutations sont liés par SHA-256 dans le manifeste v2. La gate
refuse une modification de ces fichiers, un changement de propriété entre les
deux chemins, un désaccord de verdict, une comptabilité fragmentaire incomplète
ou l’absence de réduction du travail déterministe mesuré.

La campagne v2 est conservée comme contrôle conservateur : elle relit chaque
fragment annoncé comme transporté. La campagne confirmatoire v3 mesure en plus
la réutilisation locale telle que l’API indexée la réalise. Le certificat
initial est attaché à l’objet source exact ; l’artefact cible ne peut être
obtenu que par application du delta terminal à cette source. Le vérificateur
incrémental transporte alors le préfixe sans le reparcourir et vérifie les
quatre nœuds du cône. Son travail déterministe reste de 12 unités aux cinq
tailles, tandis que le recheck complet passe de 202 à 100 002 unités. À
50 000 neurones, le certificat initial sérialisable occupe 100 087 octets et
le delta de certificat 130 octets ; 49 996 fragments sont réutilisés et quatre
recalculés. La gate v3 impose que le travail incrémental demeure borné par le
cône local, en plus de toutes les égalités et empreintes exigées en v2.
