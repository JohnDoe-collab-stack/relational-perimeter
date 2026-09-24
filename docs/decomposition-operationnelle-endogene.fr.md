# Décomposition opérationnelle endogène

## 1. Phénomène

La construction exhibe une recherche dont la décomposition opérationnelle est
un résultat du calcul plutôt qu'une donnée de sa structure de branchement.
L'ouverture produit une multiplicité structurelle. Elle ne décide pas encore
si les alternatives doivent être portées comme des obligations indépendantes
pour le critère considéré.

Cette décision dépend d'une relation reconstruite par l'exécution. Son témoin
n'est pas fourni au run. La même récursion essaie les candidats, conserve les
échecs effectifs et retourne la relation lorsqu'un essai réussit. La relation
agit alors sur toute continuation de la branche absorbée, tandis qu'une preuve
séparée établit la préservation du critère.

```text
multiplicité structurelle ≠ indépendance opérationnelle
```

La réduction ainsi obtenue n'identifie pas les alternatives et ne prouve pas
que la branche absorbée est impossible. Elle établit seulement que cette
branche n'a pas à être conservée comme obligation indépendante pour ce run et
ce critère.

## 2. Multiplicité structurelle

`ExactStructuralOpening` relie constructivement les continuations d'un parent à
la somme des continuations de deux alternatives. `split` et `merge` sont munies
de leurs deux lois de retour. L'ouverture conserve donc exactement la
multiplicité disponible sans sélectionner une branche.

`CriterionExactOpening` est une donnée distincte. Elle exprime la compatibilité
du critère avec l'ouverture, sans intégrer cette compatibilité à la structure
du carrier. Structure des continuations et évaluation de celles-ci restent
séparées.

## 3. Reconstruction exécutée

`ReconstructionSystem` fournit une liste de candidats et une fonction de
tentative. Il ne contient aucun témoin de la relation recherchée.
`exploreCandidates` parcourt la liste par récursion structurelle. Pour chaque
candidat, l'appel concret de `attempt` retourne soit `none`, soit une relation.

`ExecutedReconstruction` conserve le préfixe des `FailedAttempt`, le candidat
sélectionné, l'équation de succès et le suffixe qui n'a pas été exécuté.
`ReconstructionRun` ajoute l'équation établissant que la liste parcourue est
exactement celle qui a été extraite. Le nombre d'essais est dérivé de la trace
testée ; il n'est pas ajouté après coup.

`SuccessfulRun` donne une vue du constructeur `found` de ce même résultat. Le
paquet `EndogenousOperationalDecomposition` ne possède donc aucun champ
relationnel parallèle : `producedRelation` est une projection de cette vue, et
`relation_comes_from_executed_run` en redonne l'équation exacte avec la sortie
optionnelle du run.

Dans l'instance croissante, l'étape `n` produit `n + 1` leurres distincts puis
un candidat utile distinct de tous les leurres. Chaque leurre retourne
effectivement `none`, le dernier
candidat construit `GrowingRelation.absorb n`, et le run exécute exactement
`n + 2` essais. `growingRun_failedAttempts_exact` dérive `n + 1` échecs du
préfixe rejeté qui porte leurs preuves : chaque appel sauf le dernier appel
réussi est donc comptabilisé comme un échec. Le nombre total croît strictement
avec l'étape. À partir de l'étape `1`, ces échecs forment en outre une majorité
stricte des essais exécutés (`growingRun_failures_strictMajority`).

## 4. Action sur les continuations

`RelationalContinuationAction` donne à chaque relation directionnelle une
action totale : toute continuation de la source reçoit une continuation de la
cible. La signature ne demande aucune preuve que la continuation d'entrée
satisfait déjà le critère. L'action est donc définie avant toute conclusion sur
l'acceptation d'une alternative particulière.

`OperationalReduction.absorbLeft` compose cette action avec l'ouverture. Une
continuation provenant de la branche gauche est transportée vers la droite ;
une continuation déjà située à droite est conservée.

## 5. Préservation sans identité ni impossibilité

`CriterionPreservingAction` prouve séparément que l'action conserve le critère.
`EndogenousOperationalDecomposition.reduction_preserves` combine cette preuve
avec l'accord de l'ouverture. La fonction de réduction et sa justification
probatoire ne sont donc pas confondues.
`EndogenousOperationalDecomposition.viable_iff_after_reduction` établit alors,
pour ce critère, l'équivalence entre la viabilité de la multiplicité parente et
celle de la seule branche droite retenue. C'est cette équivalence qui autorise
à ne plus porter la branche gauche comme obligation indépendante.

Le critère concret est la positivité de la continuation : il accepte `1` et
rejette `0`. La relation `absorb n` agit par une augmentation effectivement
observable et sa préservation n'est donc pas la preuve d'une propriété constamment
vraie. L'instance prouve en outre `left ≠ right` et construit positivement une
continuation gauche qui satisfait ce critère. L'absorption opérationnelle ne
fournit ainsi ni égalité des états, ni réfutation de la branche absorbée. De
même, `none` enregistre l'échec d'un essai déterminé ; il ne devient jamais une
preuve d'inexistence de toute relation.

## 6. État produit et feedback

`ProducedOperationalState` conserve quatre sorties : résultat visible,
provenance des candidats testés, décisions relationnelles retenues et graine
suivante. `ProducedFrom` donne les quatre équations qui relient ces champs au
run spécifié. Provenance et décisions ont des types et des contenus distincts.

`FeedbackStep` reconstruit depuis l'état courant, produit l'état suivant, puis
itère en donnant exactement cette sortie à l'appel récursif. Dans l'instance,
la relation retournée produit elle-même une `GrowingDecision` et la graine de
l'étape suivante. `filterCandidatesByDecisions` consomme alors le contenu des
décisions retenues et retire de la prochaine extraction les obligations dont
l'étiquette d'étape correspond.
`GrowingPhenomenon.feedbackRunIsDecompositionRun` identifie ce run de feedback
au run porté par le témoin de décomposition. La transformation reconstruite ne
se contente donc pas d'être enregistrée : son résultat constitue les
conditions du calcul suivant.

## 7. Séparateur de non-factorisation

Pour chaque étape `n`, un premier état est la sortie canonique du run commun.
Un second conserve exactement sa sortie visible, sa provenance de candidats et
sa graine, mais efface la décision produite par la relation. La provenance ne
contient aucune copie de cette décision. Leur `visibleProjection` est exactement
égale. Pourtant, l'état retenu filtre l'obligation désignée et le run suivant exécute
`n + 2` essais, contre `n + 3` après effacement.

`nextReconstruction_notFactors n` en déduit constructivement que le résultat de
la prochaine reconstruction ne peut pas être récupéré depuis cette projection
seule. La décision n'est donc pas une annotation descriptive : son oubli
supprime une donnée effectivement consommée par le filtre suivant.

## 8. Instance périmétrale

`PerimetralComputationalState` associe une `RootedGeneratedHistory` à une
`EndpointOperationalRealization` indexée par cette histoire. La réalisation
porte positivement son endpoint exact et l'obstruction de fermeture héritée à
cet endpoint. Sa sortie visible et sa graine de reconstruction sont toutes deux
égales à `History.length` : le nombre naturel reste une lecture dérivée d'une
histoire déjà constituée et ne définit ni le périmètre ni ses occurrences.

Le raccord conserve deux mouvements distincts :

```text
GeneratedStep unaire
→ nouvelle histoire constituée
→ ouverture opérationnelle binaire
→ reconstruction exécutée
→ réduction préservée
→ état suivant produit
```

`advanceConstitution` ajoute exactement le pas produit par `generate`. Au bord
canonique, il est égal à `oneStepAfterPerimeter`.
`EndpointIndexedReconstruction` indexe le run par l'endpoint exact auquel son
état opérationnel est réalisé et porte l'obstruction de fermeture de cet
endpoint avec une équation exacte. `operationalOpening` est lu dans cette
réalisation. La relation utilisée par `reconstructedReduction` est obtenue en
appliquant `Option.map` à la sortie relationnelle du run ; elle n'est pas un
argument de l'exécuteur. `advanceOperational` produit ensuite son état depuis
ce même run indexé, avant que `advance` ne l'associe au nouvel endpoint
engendré. `advance_seed_is_derived_length` prouve que ce feedback reste aligné
sur la nouvelle histoire constituée, puis
`perimetralReconstruction_relation_exact` identifie la relation reconstruite à
chaque état aligné.

## 9. Portée exacte

Le résultat établi est relatif à une architecture, un run et un critère. Il ne
dit pas que toute recherche découvre une réduction, que toute multiplicité est
redondante, ni que l'échec d'une procédure prouve une indépendance ontologique.
Il montre positivement qu'une décomposition opérationnelle peut être constituée
pendant le calcul et que la décision produite par sa relation modifie le calcul
suivant.

L'instance croissante n'est pas présentée comme un modèle de temps machine ou
comme une classification de complexité. Ses compteurs mesurent exactement les
candidats essayés par la récursion publiée. Le théorème central concerne la
constitution de l'organisation opérationnelle, pas une revendication de classe
de complexité.

## 10. Carte des déclarations Lean

| Contenu | Déclarations principales |
|---|---|
| multiplicité structurelle exacte | `ExactStructuralOpening`, `CriterionExactOpening` |
| échecs et succès du même run | `ExecutedReconstruction`, `exploreCandidates`, `ReconstructionRun`, `SuccessfulRun` |
| relation projetée du succès exécuté | `SuccessfulRun.relation`, `relation_comes_from_executed_run`, `growingRun_relation_exact` |
| action sur toute continuation | `RelationalContinuationAction`, `OperationalReduction.absorbLeft` |
| préservation séparée et licence d'absorption | `CriterionPreservingAction`, `reduction_preserves`, `viable_iff_after_reduction` |
| distinction et viabilité de la branche absorbée | `alternativesDistinct`, `absorbedAlternative_viable` |
| candidats distincts, échecs majoritaires et travail croissant | `candidates_nodup`, `growingRun_failedAttempts_exact`, `growingRun_failures_strictMajority`, `growingRun_attempts_exact`, `growingRun_attempts_strict` |
| décision produite et filtre suivant | `feedbackInitial_decision_exact`, `secondExtraction_consumes_producedDecision` |
| même run dans la décomposition et le feedback | `GrowingPhenomenon.feedbackRunIsDecompositionRun` |
| perte par oubli de la décision | `nextReconstruction_notFactors` |
| raccord à l'endpoint périmétral | `EndpointOperationalRealization`, `EndpointIndexedReconstruction`, `perimetralReconstruction_obstruction_exact`, `advance_seed_is_derived_length`, `perimetralReconstruction_relation_exact` |
