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
| T5, proposition alignée | élimination de `RequirementSignalPath` | `ActionRealization` | une table de sorties ou un filtre aval ne remplace pas le chemin exécuté |
| T6, sensibilité | deux exigences distinctes sur un même contexte | non-trivialité publique | les propositions produites sont distinctes |
| T7, action et effet | proposition produite, `executeProducedInput`, `EffectRealization` | état initial reconfiguré | commande, résultat et successeur indépendants sont interdits |
| T8, reconfiguration récursive | certificat indexé par le système et l’entrée de l’état courant | système cible, entrée et mémoire successeure du prochain état | un certificat du système initial ne certifie pas une queue reconfigurée |
| T9, continuation | `executeReconfiguredInteractions` récure sur l’état cible produit | étape suivante et état final | la tête ne lit pas le futur ; le système produit est consommé par la queue |
| T10, oubli exact | `ReconfiguredHistoricalSource.currentState`, `reconfiguredStateRealization` | même récursion reconfigurée sous le contrat futur réduit | le contrat fixe antérieur ne remplace pas le contrat reconfiguré |
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
7. la réalisation d’oubli exact initialisée par l’état final produit par cette
   histoire ;
8. deux origines distinctes qui ont exactement cet état courant, les mêmes
   futurs reconfigurés et aucune récupération commune de leur origine.

Le raccord T8 → T9 est porté par
`ReconfiguredActionEffect.targetState` : le système cible du certificat, la
nouvelle entrée et la mémoire effectivement produite deviennent ensemble
l’index de la queue. Le raccord T9 → T10 est porté d’abord par l’égalité
`forgettingInitialState origin = continuation.finalState`, puis par
`ReconfiguredHistoricalSource.currentState` et `reconfiguredFutureContract`,
qui poursuivent depuis cet état final le même certificat dépendant à chaque
futur pas.

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
la continuation exécute exactement ses requêtes produites, que l’oubli part de
l’état final produit par cette continuation et qu’il préserve tous les futurs
reconfigurés couverts.

Six fixtures négatives vérifient exactement que :

- le certificat du système public initial ne certifie pas un état arbitraire ;
- le contrat futur de l’ancien système fixe ne remplace pas le contrat
  reconfiguré ;
- `True` ne remplace pas le certificat dépendant final ;
- la mémoire antérieure à l’action ne remplace pas son successeur produit ;
- l’état initial ne remplace pas l’état final produit à l’entrée de l’oubli ;
- un certificat construit séparément ne remplace pas le résultat du
  certificateur canonique de l’étape.

## État actuel des vérifications

- construction ciblée de tous les nouveaux modules : réussie ;
- tests positifs neuronaux : réussis après adaptation à l’interface dépendante ;
- six nouvelles fixtures négatives : rejetées au diagnostic et au site
  enregistrés ;
- inventaire de stratification : 332 modules, tous contrôlés, aucun orphelin ;
- tous les nouveaux audits `#print axioms` : aucun axiome ;
- construction globale : réussie, 401 tâches, audit exhaustif de 32 542
  constantes sur 398 modules, aucune déclaration manuscrite dépendante d’un
  axiome ;
- vérificateur global : volontairement bloqué par la fraîcheur du registre
  scientifique après modification de `scripts/stratification.tsv`.

Le blocage `STALE_SOURCE: GODEL_OPERATIONAL_RUNTIME_CLOSURE_OBSTRUCTION` ne
doit pas être neutralisé par une mise à jour mécanique d’empreinte. Conformément
au protocole du dépôt, une nouvelle version de l’instantané scientifique ne
peut être établie qu’après création d’un commit explicitement autorisé. Tant
que cette étape de publication n’a pas eu lieu, la branche de travail n’est pas
déclarée prête à fusionner.
