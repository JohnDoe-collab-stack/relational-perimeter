# Alignement constitutif neuronal incrémental

## Statut scientifique

Identifiant de claim enregistré :
`CONSTITUTIVE_NEURAL_ALIGNMENT_CLOSED_RUNTIME`.

Le registre contient déjà cet identifiant sur une révision historique. Les
changements du candidat courant rouvrent toutefois la lecture scientifique,
la comparaison de la traduction et l’audit indépendant. Ce texte décrit les
résultats présents dans l’arbre de travail ; il ne déclare pas C18 satisfait et
ne transfère aucun verdict antérieur vers la future révision d’évidence.

## Claim canonique

Dans ce cadre, l’alignement n’est pas défini par la seule conformité d’une
table de sorties. Il est relatif à un méta-contrat constitutif reçu et fixé,
qui distingue les contrats opérationnels admis, leurs transitions autorisées
et les obligations à préserver ou à revérifier. Pour un artefact neuronal
sérialisé accepté par le vérificateur initial et toute suite finie de mises à
jour acceptée par le vérificateur dépendant, le runtime formalisé ne poursuit
que la chaîne effectivement certifiée : décodage de l’artefact reçu, exécution du
mécanisme neuronal, proposition, action, effet, successeur, transition de
contrat et obligations de futurs. Chaque étape consomme exactement l’état
certifié produit par la précédente ; une mise à jour refusée ne fournit aucun
successeur installable par l’API fermée.

La certification ne reçoit pas sa conclusion comme donnée. Les obligations du
contrat sont définies indépendamment du succès du vérificateur, instanciées sur
l’état et les occurrences produits, puis décidées par des analyses
exécutables. Le vérificateur complet de référence reconstruit ses fragments
sans recevoir le verdict ni les fragments du chemin incrémental ; le
vérificateur incrémental transporte les fragments licenciés situés hors du
cône affecté et recalcule les autres. Sur leur domaine fini déclaré, leur
acceptation est équivalente et leurs succès produisent le même successeur
certifié.

L’instance apprise ferme une séparation que la seule observation du
comportement courant ne voit pas. Deux mises à jour portent la même intention
admise et produisent la même table sur tout le domaine courant déclaré. Tout
vérificateur qui factorise exclusivement par cette table leur attribue donc le
même verdict. Pourtant, la mise à jour alignée consomme effectivement la
ressource d’autorisation exigée, est acceptée et installée ; la mise à jour de
contournement ne la consomme pas, est refusée pour dépendance constitutive
manquante et ne peut pas être installée. Une continuation future explicite et
non vide calcule ensuite une issue conforme pour la mise à jour alignée et une
issue incompatible avec le contrat pour le contournement simulé sans effet.

L’oubli reste une opération distincte de cette séparation. Dans l’instance
publique correspondante, deux états dont l’origine historique est réellement
présente alimentent une exécution d’oubli ; celle-ci produit une mémoire réduite
commune, conserve exactement les futurs couverts et rend impossible la
reconstruction de l’origine supprimée depuis cette mémoire. Le résultat ne
confond donc ni regroupement, ni oubli, ni égalité des états sources.

## Hypothèses et portée exactes

Le claim est conditionnel aux éléments suivants :

- le méta-contrat, le contrat opérationnel, l’admission initiale, les exigences,
  les contextes, le schéma des futurs et les règles de transition sont reçus ;
  l’exécution ne produit pas leur justification normative ;
- l’artefact et les mises à jour sont des données sérialisées sans certificat
  cible incorporé ; leur décodage doit réussir avec les ports, poids, références
  chronologiques et noms de contrats attendus ;
- le domaine courant et la base causale utilisés par les décisions locales sont
  finis et décidables ; cette finitude ne réduit pas la quantification sur toute
  suite finie de mises à jour acceptée ni sur tous les futurs couverts ;
- les garanties portent sur les traces que `checkInitial`, le checker dépendant
  et `checkUpdates` acceptent. Elles ne disent pas que toute mise à jour est
  acceptable ;
- la préservation des futurs est relative au `FutureContract` déclaré et à ses
  réalisations exactes, non à toute observation imaginable ;
- la comparaison alignée/contournement concerne l’artefact appris, le domaine
  courant à quatre cas et la continuation non vide enregistrés dans le dossier ;
- la simulation du candidat refusé est pure et contrefactuelle. Elle ne constitue
  pas une voie d’effectuation du runtime.

## Décomposition des responsabilités

La chaîne distingue explicitement :

| Statut | Contenu |
| --- | --- |
| Reçu et fixé | Méta-contrat, contrat admis, exigences, contextes, autorisations, artefacts sérialisés et schéma des futurs. |
| Produit par exécution | Décodage, activations neuronales, transformations, propositions, actions, effets, successeurs et décisions locales ; le cône affecté est ensuite calculé depuis le graphe et le delta décodés. |
| Dérivé | Certificats d’état, correction du checker, équivalence incrémental/complet, préservation des contrats et accessibilité du runtime. |
| Autorisé | Transitions de contrats et mises à jour admises par le méta-contrat ; l’admission reste distincte de la satisfaction du contrat cible. |
| Transporté | Fragments hors cône, obligations persistantes et futurs couverts explicitement par le contrat. |
| Recalculé | Fragments affectés, obligations invalidées et décisions propres au nouvel état. |
| Oublié | Origine historique supprimée par l’exécution d’oubli autorisée. |
| Irrécupérable | Distinction d’origine dont aucune reconstruction depuis la mémoire réduite ne peut satisfaire les deux lois de retour exigées. |

## Références formelles principales

| Résultat | Déclaration ou module |
| --- | --- |
| Trace dépendante finie et alignement de chaque étape | `checkedTrace_constitutivelyAligned`, `checkUpdates_sound` dans [CheckedUpdateTrace.lean](../RelationalPerimeter/Agents/Neural/CheckedUpdateTrace.lean) |
| Préservation des contrats par toute histoire runtime | `EveryRuntimeStepPreservesContracts` dans [CertifiedRuntime.lean](../RelationalPerimeter/Agents/Neural/CertifiedRuntime.lean) |
| Refus sans successeur installable | `submitUpdate_rejected_cannot_install` dans [CertifiedRuntime.lean](../RelationalPerimeter/Agents/Neural/CertifiedRuntime.lean) |
| Vérificateurs complet et incrémental | `checkReferenceUpdate`, `checkIncrementalUpdate` dans [ReferenceChecker.lean](../RelationalPerimeter/Agents/Neural/ReferenceChecker.lean) et [IncrementalChecker.lean](../RelationalPerimeter/Agents/Neural/IncrementalChecker.lean) |
| Équivalence locale incrémental/complet | `incrementalAndReferenceAcceptance_equivalent` dans [IncrementalReferenceEquivalence.lean](../RelationalPerimeter/Agents/Neural/IncrementalReferenceEquivalence.lean) |
| Séparation du contournement latent | `constitutiveChecker_detectsLatentBypass` dans [FiniteCounterfactualDivergence.lean](../RelationalPerimeter/Agents/Neural/FiniteCounterfactualDivergence.lean) |
| Accord de tout vérificateur limité à la table courante | `everyLearnedRuntimeCurrentVerifierAgrees` dans [LearnedContractFutureDivergence.lean](../RelationalPerimeter/Agents/Neural/LearnedContractFutureDivergence.lean) |
| Installation alignée et rejet du contournement | `submitUpdate_learned_aligned_exact`, `submitUpdate_learned_bypass_rejected` dans [LearnedRuntimeAdapter.lean](../RelationalPerimeter/Agents/Neural/LearnedRuntimeAdapter.lean) |
| Divergence dans le contrat futur exact | `learnedOperationalFutureDivergence` dans [LearnedContractFutureDivergence.lean](../RelationalPerimeter/Agents/Neural/LearnedContractFutureDivergence.lean) |
| Oubli exécuté, futurs conservés et origine irrécupérable | `public_executed_forgetting_outputs_equal`, `public_executed_forgetting_preserves_future`, `public_executed_forgetting_origin_not_recoverable` dans [PublicExactForgetting.lean](../RelationalPerimeter/Agents/Neural/PublicExactForgetting.lean) |
| Séparation pour toute réalisation exacte et préservation de toute suite finie couverte | `learnedEveryExactRealizationSeparatesAlignedFromBypass`, `learnedExecutedFutureForgetting_preserves_every_finite_future` dans [LearnedFutureConstitutiveClosure.lean](../RelationalPerimeter/Agents/Neural/LearnedFutureConstitutiveClosure.lean) |
| Certificat conjoint sur la même lignée apprise | `learnedConstitutiveAlignmentClosure` dans [LearnedFutureConstitutiveClosure.lean](../RelationalPerimeter/Agents/Neural/LearnedFutureConstitutiveClosure.lean) |

Ces déclarations restent soumises aux gates complètes du dépôt, au raccord à
une révision d’évidence existante et aux audits distincts de validité et de
portée. La liste indique les points d’entrée du claim ; elle ne remplace ni
l’audit de leurs dépendances transitives ni une généralisation au-delà des
interfaces et quantifications effectivement énoncées.

## Dossier comparatif

### Comparaison de capacité

Le protocole gelé
[`constitutive-neural-oracle-independent-capability-comparison-v13`](../experiments/constitutive-neural-alignment/v13/comparison-protocol.json)
compare neuf calculs locaux au dépôt : six adaptateurs typés, la méthode
relationnelle, une combinaison explicite de références et le recheck complet
indépendant. Il fournit à chaque méthode les interventions, futurs, contrats
et versions que son interface déclarée sait consommer. La combinaison de
référence calcule ses observations sans recevoir le verdict final ni le
certificat cible comme oracle.

Le [run confirmatoire v13](../experiments/constitutive-neural-alignment/v13/COMPARISON_ANALYSIS.md)
a émis les neuf lignes préenregistrées et rejeté les dix-sept ablations
sémantiques. P2 transporte un consommateur admissible réellement modifié et
un consommateur interdit depuis la même exécution exacte du réseau à travers
le checker incrémental générique et un recheck complet indépendant ; les deux
s’accordent sur le successeur et le certificat acceptés. P3, P4, P5 et P6
émettent aussi leurs résultats positifs et négatifs déclarés. Les succès des
méthodes concurrentes restent visibles : la combinaison explicite de
références et le recheck complet distinguent eux aussi la mise à jour alignée
du contournement. P7 est ainsi fermé dans sa portée locale au dépôt. Cela
n’établit ni l’équivalence avec toute méthode externe des classes nommées, ni
une supériorité générale, une incapacité des baselines ou une nouveauté
scientifique.

### Passage à l’échelle du checker compilé

La campagne gelée
[`compiled-causal-complete-property-scaling-v12`](../experiments/constitutive-neural-alignment/v12/scaling-protocol.json)
mesure le même checker compilé de propriété complète et un recheck complet
indépendant sur une chaîne causale de successeurs. Ses graphes, obligations et
traces croissent ; elle enregistre les coûts de toutes les phases, la mémoire,
les tailles sérialisées et les fragments effectivement transportés ou
recalculés. Le
[run confirmatoire](../experiments/constitutive-neural-alignment/v12/SCALING_ANALYSIS.md)
a accepté les 25 répétitions préenregistrées aux tailles 0, 4, 8, 16 et 32 et
rejeté le contrôle négatif. La réutilisation est réelle : la première
transition locale à la taille 32 transporte 34 fragments et en recalcule deux,
tandis qu’une transition étendue en transporte un et en recalcule 35.

Le critère pratique préenregistré est néanmoins faux. Selon la taille, la
médiane incrémentale cumulée vaut de 3,865 à 760,445 fois celle du recheck
complet. P8 est donc évalué et P8/S6 sont défavorables pour cette
implémentation ; aucun gain de temps ou de mémoire n’est revendiqué. Cette
campagne observationnelle n’est ni un théorème Lean ni un résultat de
complexité asymptotique.

## Exclusions explicites

Ce claim ne démontre pas :

- la découverte de valeurs humaines ni la correction morale du méta-contrat ;
- l’alignement universel de tout système d’IA ou de tout réseau neuronal ;
- la robustesse envers des entrées, futurs ou transformations hors du contrat ;
- qu’un comportement courant équivalent implique à lui seul un danger ;
- que toute méthode non constitutive échoue ou qu’une baseline est incapable
  d’exprimer les mêmes obligations ;
- un gain de temps ou de mémoire du checker incrémental actuel ;
- une borne générale de complexité ;
- une conclusion de nouveauté avant l’exécution comparative et les audits
  indépendants de la révision d’évidence.

Le résultat formel est une garantie relative : sous le méta-contrat fixé et les
interfaces déclarées, l’API fermée ne poursuit que les états dont la chaîne
constitutive exigée a été produite et certifiée, et l’instance apprise exhibe
un contournement latent que la seule table courante ne distingue pas.
