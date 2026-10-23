# Alignement constitutif neuronal incrémental

## Statut scientifique

Identifiant de claim proposé :
`CONSTITUTIVE_NEURAL_ALIGNMENT_CLOSED_RUNTIME`.

Ce texte est le passage canonique français préparé avant le commit d’évidence,
l’enregistrement du claim et les audits indépendants. Il décrit les résultats
présents dans l’arbre de travail ; il ne déclare pas encore C18 satisfait et ne
remplace pas la révision exacte qui devra être enregistrée après le gel.

## Claim canonique

Dans ce cadre, l’alignement n’est pas défini par la seule conformité d’une
table de sorties. Il est relatif à un méta-contrat constitutif reçu et fixé,
qui distingue les contrats opérationnels admis, leurs transitions autorisées
et les obligations à préserver ou à revérifier. Pour un artefact neuronal
sérialisé accepté par le vérificateur initial et toute suite finie de mises à
jour acceptée par le vérificateur dépendant, le runtime ne poursuit que la
chaîne effectivement certifiée : décodage de l’artefact reçu, exécution du
mécanisme neuronal, proposition, action, effet, successeur, transition de
contrat et obligations de futurs. Chaque étape consomme exactement l’état
certifié produit par la précédente ; une mise à jour refusée ne fournit aucun
successeur installable par l’API fermée.

La certification ne reçoit pas sa conclusion comme donnée. Les obligations du
contrat sont définies indépendamment du succès du vérificateur, instanciées sur
l’état et les occurrences produits, puis décidées par des analyses
exécutables. Le vérificateur complet recalcule tous les fragments ; le
vérificateur incrémental transporte uniquement les fragments situés hors du
cône affecté et recalcule les autres. Sur leur domaine local déclaré, leur
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
| Produit par exécution | Décodage, activations neuronales, transformations, propositions, actions, effets, successeurs, décisions locales et cônes affectés. |
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

Ces déclarations restent soumises aux gates complètes du dépôt et au futur
commit d’évidence. La liste indique les points d’entrée du claim ; elle ne
remplace pas l’audit de leurs dépendances transitives.

## Dossier comparatif

### Comparaison de capacité

Le protocole
[`constitutive-neural-capability-comparison-v6`](../experiments/constitutive-neural-alignment/v6/comparison-protocol.json)
fige un même artefact appris, une même paire de mises à jour, six adaptateurs
typés et huit capacités. Les six classes sont : vérification extensionnelle du
comportement courant, analyse causale interventionnelle d’un réseau fixe,
filtrage d’action avant exécution, système auto-adaptatif garanti, vérification
neuronale incrémentale avec réemploi de preuve, et propagation de certificats
sur une chaîne de déploiement.

Le statut actuel est strict : v6 est un protocole historique dont les
empreintes ne correspondent plus aux sources du candidat courant. Aucun run
confirmatoire v6 n’a été exécuté et aucun fichier de résultat comparatif
n’existe. Une nouvelle version devra figer les adaptateurs et leurs références
avant toute exécution confirmatoire. Il est donc interdit d’en déduire une
supériorité générale, une incapacité d’une baseline ou une nouveauté
scientifique. Le seul contraste formel déjà fermé à ce niveau est celui des
vérificateurs dont le verdict factorise exclusivement par la table courante
finie : ils ne distinguent pas les deux candidats, alors que le checker
constitutif les distingue par la dépendance exécutée et le contrat futur.

### Passage à l’échelle du checker compilé

La campagne historique
[`compiled-parameterized-neural-scaling-v8`](../experiments/constitutive-neural-alignment/v8/SCALING_ANALYSIS.md)
porte sur le même checker Lean compilé, pour sept tailles de 0 à 80, cinq
répétitions mesurées et 210 mises à jour acceptées. Elle établit une
réutilisation structurelle réelle : lors d’une transition locale à la taille
80, 83 fragments sont transportés et un seul est recalculé.

Elle n’établit aucun gain pratique de temps. À la taille 80, la médiane de la
trace incrémentale est de 70 777,626 ms, contre 10,522 ms pour le recheck
complet ; le critère de gain préenregistré est faux. Aucune loi asymptotique,
aucune économie générale et aucune généralisation à d’autres familles ne sont
revendiquées. Ses empreintes sont conservées sans être réécrites ; elles ne
valident pas le candidat courant. La campagne exploratoire rejouée sur celui-ci
confirme la réutilisation structurelle mais reste non figée, sans mesure mémoire
exploitable et avec des temps incrémentaux défavorables. P8 et S6 restent donc
ouverts pour une nouvelle campagne préenregistrée.

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
