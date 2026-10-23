# L1 — Obligations autonomes et transitions attendues

## Statut

Ce document spécifie le lot L1 de la correction ordonnée. Il ne modifie pas
les contrats historiques et ne déclare pas fermés L2–L12. La spécification
typée correspondante est dans
`RelationalPerimeter/Agents/Neural/AutonomousContractTransitions.lean`.

## 1. Ordre constitutif fixé

L'ordre est désormais explicite dans les types :

1. le méta-contrat fournit un contrat opérationnel admis et ses permissions de
   transition ;
2. le contrat fixe les sept familles d'obligations et son `futureContract` ;
3. une exécution produit un état exact ;
4. les applications `...At state` instancient les sept familles sur cet état ;
5. les témoins de `ContractObligationsAt` prouvent ces instances ;
6. `ContractFutureObservationAt` produit la source d'observation depuis l'état,
   sans recevoir de projection mémoire ni de réalisation exacte ;
7. une réalisation exacte éventuelle est examinée seulement ensuite ;
8. une transition transporte les obligations persistantes et revérifie les
   obligations invalidées avant qu'un `CheckedUpdate` puisse être construit.

Le succès d'un checker complet n'apparaît dans aucun des types introduits par
L1.

## 2. Cartographie formation / exécution / preuve / transport

| Niveau | Formation reçue ou fixée | Exécution ou instanciation | Preuve construite | Transport ou consommation |
| --- | --- | --- | --- | --- |
| Contrat | `ConstitutiveMetaContract.operational` et `ConstitutiveContract` | état de `ReconfiguredExecutionState` | admission du membre du méta-contrat | `OperationalContractTransition` |
| Exigence | `requirementEncoding` | `requirementEncodingAt state` | `ContractObligationsAt.requirementEncoding` | certificat cible ou revérification |
| Causalité | `causalCondition` | `causalConditionAt state` | `ContractObligationsAt.causalCondition` | certificat cible ou revérification |
| Proposition/action | `proposalActionPreservation` | `proposalActionPreservationAt state` | `ContractObligationsAt.proposalActionPreservation` | certificat cible ou revérification |
| Autorisation | `authorizationAdmission` | `authorizationAdmissionAt state` | `ContractObligationsAt.authorizationAdmission` | revérification sous le contrat cible |
| Effet | `effectSatisfaction` | `effectSatisfactionAt state` | `ContractObligationsAt.effectSatisfaction` | certificat du successeur exact |
| Futurs couverts | `coveredFuture` | `coveredFutureAt state requests` | `ContractObligationsAt.coveredFuture` | réalisation du `futureContract` fixée séparément |
| Histoire | `historicalPolicy` | `historicalPolicyAt state` | `ContractObligationsAt.historicalPolicy` | transport justifié ou revérification |
| Observation future | `futureContract` | `futureSourceOfState state` | `ContractFutureObservationAt` | toute réalisation exacte est quantifiée après fixation de la source |
| Transition | `TransitionPermission current next` | `ExecutedStateTransition ... current.state targetState` | `AutonomousTransitionObligations` | `transportedPersistent` et `rechecked` |

`StateConstitutiveCertificate.obligationsAt` projette les sept témoins déjà
consommés par un certificat existant. Il ne projette pas la réalisation future :
cette réalisation reste une couche ultérieure et séparée.

## 3. Conditions autonomes de reconfiguration

`AutonomousReconfigurationConditions builder sourceSystem sourceInput
nextInput` fixe :

- le système source exact ;
- le run exact `sourceSystem.run sourceInput` ;
- la nouvelle exigence `nextInput.requirement` ;
- le nouveau contexte `nextInput.context` ;
- l'autorisation incorporée indexée par ce même `nextInput`.

`AutonomousReconfigurationConditions.execute` appelle le constructeur
`reconfigure` existant. Le théorème `executed_target_exact` montre que le
système cible est celui produit par `builder.build` depuis ces données exactes.
Aucun port n'est renommé pour remplacer une dépendance causale.

Les contrôles négatifs refusent une autorisation provenant d'une autre
exigence.

## 4. Indépendance du schéma d'observation — RC3

`contractFutureObservationAt state` reçoit seulement le contrat implicite et
l'état produit. Sa source est exactement `contract.futureSourceOfState state`.
Ni une projection candidate, ni une mémoire réduite, ni une preuve
d'exactitude, ni un verdict de checker ne sont des paramètres de ce producteur.

`ContractFutureObservationAt.outcome_exact` quantifie ensuite sur une
`ExactRealization` arbitraire du `futureContract` déjà fixé. Cette direction de
dépendance interdit de redéfinir l'obligation source après lecture de la
réalisation candidate.

Le contrôle négatif correspondant refuse de remplacer la source indexée par
la source d'un autre état exécuté.

## 5. Interfaces indexées par l'agent courant

`AutonomousTransitionObligations` et `CurrentAgentTransitionInterface` sont
indexés par :

- le méta-contrat ;
- le nom du contrat courant ;
- le `CheckedAgent` courant exact ;
- le contrat cible et la transition exacte, lorsqu'ils existent.

Une interface locale fixe son type `LocalConditions` avant l'exécution de sa
décision. La décision retourne soit un témoin positif de ces conditions, soit
une réfutation constructive. Elle ne reçoit aucun succès de recheck complet.

## 6. Transitions après oubli

`ForgottenCurrentAgent current` est la mémoire réduite produite par la
réalisation future déjà certifiée de l'agent courant. Les requêtes admises sont
exclusivement :

1. `continueCurrent input` : la permission est le témoin `Allow` du contrat
   réduit déjà fixé ;
2. `changeContract nextContract` : la permission contient un
   `JustifiedPostForgettingTransition` du même méta-contrat.

Une transition de contrat après oubli doit fournir les témoins sources des
obligations persistantes. Leur cible est calculée uniquement par
`OperationalContractTransition.transport`. Les obligations invalidées sont
reconstruites uniquement par `OperationalContractTransition.recheck`.

`PostForgettingDecision` impose une alternative explicite : permission
construite ou réfutation constructive de cette permission. Une récupération
historique ou un passage vers un contrat non autorisé doit donc être refusé ;
il ne peut pas être simulé par une API parallèle.

Le contrôle négatif correspondant refuse la transition inverse
`.reconfigured -> .initial`, absente du méta-contrat public.

## 7. Portée exacte de L1

L1 ferme la spécification des origines déclarées de RC1 et la frontière de
dépendance de RC3. Il rend explicites les transitions que les lots ultérieurs
doivent produire et consommer.

L1 ne prétend pas encore :

- que l'instance apprise construit déjà toutes les transitions après oubli ;
- que les mêmes occurrences du run maître sont raccordées de bout en bout ;
- que les checkers installent déjà toutes les transitions successives ;
- que RC2, RC4, RC5, RC6 ou G1–G10 sont conjointement fermés.

Si L2–L8 imposent de modifier une instance opérationnelle, les preuves,
fixtures, revues et empreintes de cette instance seront rouvertes. Les contrats
et résultats historiques ne seront pas réécrits rétrospectivement.

## 8. Contrôles du lot

- module constructif : `AutonomousContractTransitions.lean` ;
- réalisation positive :
  `Tests/Mechanisms/NeuralL1AutonomousObligations.lean` ;
- refus d'une source d'observation étrangère ;
- refus d'une autorisation attachée à une autre exigence ;
- refus d'une transition inversant la permission du méta-contrat ;
- audit axiomatique final unique dans chaque fichier Lean ;
- absence de `noncomputable`, `Classical`, `axiom` et `sorry` dans le lot.
