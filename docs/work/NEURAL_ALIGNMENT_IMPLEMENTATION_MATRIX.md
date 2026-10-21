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
→ M19 public root
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
- 86 fixtures négatives : toutes rejetées au diagnostic et au site
  enregistrés, dont la substitution du programme d’oubli constant et celle de
  l’état complet à la mémoire réduite ;
- inventaire de stratification : 332 modules, tous contrôlés, aucun orphelin ;
- tous les nouveaux audits `#print axioms` : aucun axiome ;
- construction globale : réussie, 401 tâches, audit exhaustif de 33 175
  constantes sur 398 modules, aucune déclaration manuscrite dépendante d’un
  axiome ;
- registre scientifique : quatre fermetures renouvelées sur le commit stable
  `13f9e0977fcd79ae47504fc32400a90a3b17eeb1`, 23 claims et 253 déclarations
  résolus sans empreinte périmée ;
- vérificateurs globaux : `verify.ps1` et `verify.sh` terminent intégralement
  avec succès sur le registre renouvelé.
