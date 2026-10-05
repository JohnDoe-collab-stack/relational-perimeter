# Agent constitutif de recherche et de restitution

Cette instance prolonge le calcul public existant par une session interactive.
Une demande peut consulter une production, faire poursuivre le moteur, obtenir
une production encore absente ou soumettre une valeur à autorisation. Le
périmètre reçu gouverne les réponses ; leurs valeurs viennent des continuations
effectivement produites. La mémoire de reprise permet de continuer ce travail
sans permettre de reconstruire uniformément le profil source initial.

Il s’agit d’un agent symbolique construit en Lean, pas d’un modèle de langage,
d’un solveur SAT général ou d’un résultat d’alignement humain général. La cible
scientifique antérieure et les quatre modules fondamentaux restent inchangés.

## Entrée et exigence

`publicAgent input scope selectionCode` reçoit un périmètre non vide de
variables et un code de sélection. Il forme un seul résultat maître public,
puis interprète ce code sur ses rôles réellement constitués. Un code de mauvaise
longueur et un périmètre vide donnent des refus distincts. Le décodage parcourt
une histoire de rôles, sans énumérer les profils.

`InitializationCertificate` relie le résultat exact de `prepare` au périmètre
reçu, au décodage du code réellement fourni et à la mémoire initialisée.
`Prepared.certificate` réunit ce raccord et le certificat de continuation sur
le même maître. Le code et le profil décodé restent dans ce paquet scientifique,
pas dans la mémoire de reprise. Les refus de sélection invalide et de mauvaise
longueur ont leurs lois publiques.

Le périmètre ne fournit aucune réponse attendue. Il détermine quelles variables
peuvent être lues, pas celles choisies par la découverte. Deux périmètres peuvent
donc changer l’autorisation d’une même lecture sans changer sa vérité. Les
doublons de variables ne créent pas de droit supplémentaire.

Les demandes sont :

| Demande | Effet |
| --- | --- |
| `advance steps` | Exécute les étapes réelles demandées. |
| `inspect handle var` | Lit une cible existante, si la variable est permise. |
| `obtain handle var` | Produit les étapes manquantes, puis restitue la lecture permise. |
| `propose handle var value` | Autorise uniquement une valeur égale à la lecture réelle. |

Hors périmètre, cible absente et valeur incorrecte sont des motifs de refus
distincts. Pour `obtain`, une variable permise conduit à une cible présente et à
sa réponse : la correction n’est pas obtenue en refusant toutes les demandes.

## Productions et garantie des réponses

Le registre initial contient une composante de la cible normalisée par rôle,
avec son contexte et son acceptation propres. Chaque reprise ajoute la sortie
`production.built.stage.application.output` de l’étape exécutée. Les cibles
initiales et reprises n’ont pas nécessairement le même contexte d’acceptation.
Une lecture booléenne n’est pas présentée comme une preuve SAT globale.

`TargetOrigin` est un témoin dépendant de la continuation : il désigne la
production locale dont elle est la sortie, et non une simple étiquette. La
fabrique initiale exige l’accord exact de la cible avec les sorties des rôles
exécutés ; l’acceptation seule ne permet pas d’y insérer une autre continuation.
Ce témoin ne conserve pas le choix du profil source normalisé.

L'acceptation de chaque cible est obtenue en éliminant son `TargetOrigin` :
elle vient de la licence de normalisation ou de la sortie de l'étape reprise.
`AnswerTarget` ne contient plus une preuve d'acceptation indépendante. Cette
garantie est ensuite consommée dans le critère de restitution.

Un handle numérique est une adresse locale à la session, pas une occurrence
constituée à lui seul. Sa résolution construit une référence typée à une cible
réelle. L’ajout en fin de registre préserve les anciens handles ; les références
des supports historiques sont, elles, transportées par les extensions réelles.
La taille du registre consultable n’est pas la largeur d’obligations indépendantes.

`History.realization` forme le support riche des cibles par des producteurs à
ports typés, depuis la normalisation et les étapes réelles. Son accord relie
chaque référence du registre à la référence historique qui lit cette cible.
`History.handle_transport` ferme le raccord entre l’extension du registre et
l’extension du support ; les lectures, l’injectivité des références et le
décalage de leurs positions sont prouvés séparément. Ce support riche n’est
pas conservé dans la mémoire runtime.

`HistoricalFormation` suit le support lui-même, avec ses ports et son arbre de
formation. Seul le couple initial maître/profil est donné. Normalisation,
curseur, composantes et cibles reprises sont ajoutés par leurs producteurs.
Un support contenant une référence de cible ne peut pas être déclaré donné
avec les mêmes valeurs. `MaterialReading` porte cette formation et les lectures
effectives ; `RichOperation` porte cette lecture et la décision qui en découle.
Son résultat est éliminé de ces objets, puis raccordé au résultat runtime.

Avec `r` entrées et le handle `h`, lorsque la variable est autorisée et que
le handle manque, `obtain` produit exactement `h + 1 - r` étapes et le registre
atteint exactement `h + 1` entrées. Si le handle existe déjà, aucune étape
n’est produite. Les lois portent sur les événements du worker réel. Un refus
laisse la mémoire entière inchangée.

`performCertified` construit conjointement la mémoire suivante, l’événement et
le témoin de réponse. Une décision locale est partagée entre son message et son
autorisation. `interactionProducer` lit la mémoire courante et la demande par
ses ports ; `executeProducedInput` restitue cette production entière. Les API
simples projettent ses données, sans exécuter un second décideur.

`ResponseEvidence` est une spécification indépendante du répondeur : elle exige
une permission, une occurrence et un accord avec sa valeur, ou les faits précis
justifiant un refus. Elle n’est pas définie comme « la réponse choisie est correcte ».

## Raccord avec l’histoire riche

La source scientifique conserve le profil initial et l’histoire des ressources.
Son interprète lit les cibles de cette histoire, non les réponses projetées du
runtime. Les lois de transition, d’événement, de lecture et d’admission sont
démontrées séparément, puis composées pour toute liste finie de demandes.

Les lectures et autorisations riches consomment les valeurs du support réalisé,
puis leur accord avec les entrées réduites. `FollowedStages` suit aussi chaque
étape interne d’une demande ; le certificat ne s’arrête pas aux frontières
entre demandes.

Chaque `InternalStepAgreement` ferme l'accord avec la production vivante,
la cible ajoutée et son acceptation. Il contient deux extensions distinctes :
celle du support courant du moteur et celle du support historique des cibles.
`FollowedStages.engineTransport` et `historicalTransport` composent ces
extensions jusqu'au dernier état ; leurs lectures, injectivité et positions
sont celles des extensions réalisées. Les événements et la mémoire finale du
suivi sont prouvés égaux à ceux des étapes effectivement exécutées.

Les permissions riches se réfèrent au périmètre reçu ; les permissions runtime
à sa réalisation portée par les ressources. Leur passage possède les deux lois
de retour sur les témoins, pas seulement deux implications de validité.

La tête utilise seulement la mémoire et la demande courantes. Aucun paramètre
de demandes futures n’entre dans son producteur. Le certificat ferme son
exactitude, son indépendance de l’horizon et les accords de la continuation.

`ReplyCriterion` exige, pour une réponse positive, une autorisation et
l'acceptation de sa cible dans son contexte propre. `FiniteResponseCriterion`
applique cette exigence à chaque réponse de l'exécuteur réel. Le suivi fini
implique ce contrat ; le champ `Certificate.satisfaction` consomme cette
démonstration. Aucune prémisse extérieure d'acceptation n'est demandée au client.

## Oubli et portée

`Memory` contient exactement l’exigence, le moteur vivant et le registre de
cibles. `Session` ne contient que cette mémoire. Ni le code initial ni un champ
de profil source n’y est conservé. Le paquet scientifique `Prepared` et l’histoire
riche restent séparés de la session runtime ; ils ne sont pas consultés pour agir.

La factorisation par la cible normalisée donne l’égalité des mémoires complètes
de deux profils sources démontrés distincts. Il n’existe donc aucune fonction
Lean de cette mémoire vers le profil source qui reconstruise uniformément
toutes les initialisations. Les mêmes demandes futures donnent les mêmes
mémoires, réponses et événements ; les admissions sont conservées et reflétées.

Cet oubli porte sur la distinction du profil initial dans cette mémoire et sous
ce contrat. Il ne supprime ni la provenance encore nécessaire à la découverte,
ni toutes les histoires chronologiques. Ce n’est pas une preuve de mémoire
physique constante, de coût polynomial ou de sécurité contre l’inspection externe
des fermetures compilées. Le registre croît pour conserver les lectures promises.

Le contrôle du code compilé exclut les archives riches et l’énumération globale
des profils du chemin de reprise. Le moteur réutilisé construit encore une
lecture locale de ses deux occurrences après l’action ; cette lecture ne choisit
pas la découverte. Celle-ci fait l’objet d’un contrôle de dépendances séparé.

Ce contrôle couvre `Session.execute`, `produce` et `executeAll`, ainsi que
l'initialisation. Il suit les auxiliaires, les alias et les applications de
fermetures résolues. Les bornes d'appels portent sur une entrée ou un dépliage
structurel explicite, pas sur une exécution entière de longueur arbitraire.
Un appel indirect nécessaire non résolu est un échec du contrôle, pas un coût
nul. Les refus attendus sont vérifiés à partir des diagnostics JSON de Lean,
avec fichier, ligne, colonne et motif figés ; une erreur supplémentaire ou un
texte imprimé ne valide pas la fixture.

La politique de source des fixtures exclut aussi les commandes et tactiques
capables de fabriquer un diagnostic. Elle distingue les littéraux de caractère
des chaînes et reconnaît les commentaires Lean imbriqués, puis contrôle les
tokens hors de ces régions, même après un commentaire ou un modificateur.
Les chaînes interpolées et les formes de caractère non prises en charge sont
refusées. Ce contrôle restreint ne prétend pas sécuriser du Lean arbitraire.
Les deux scripts de vérification exécutent automatiquement les 864 cas de la
matrice lexicale et les contrôles simulés des diagnostics et interruptions.
La suite complète des deux wrappers se lance séparément avec
`python scripts/test-expected-failure-gates.py --output <répertoire neuf>`.

## Déclarations et reproduction

Tous les modules sont accessibles depuis `import RelationalPerimeter`.

| Obligation | Déclaration dans `ConstitutiveSearch.Agent` |
| --- | --- |
| Formation du périmètre | `receive`, `Requirement.scope_exact` |
| Codes réellement interprétés | `decode_encode`, `initialized_codes_admitted` |
| Initialisation certifiée avec son entrée | `InitializationCertificate`, `Prepared.prepare_exact`, `initialize_invalid_selection`, `initialize_wrong_length` |
| Cibles effectives | `initialTargets`, `resumedTarget`, `executed_step_register_exact` |
| Réponse et témoin partagés | `performCertified`, `executeProducedInput`, `executedEvidence` |
| Réponses admises et erronées | `candidate_authorization_exact`, `admitted_inspection_returns`, `correct_candidate_returns`, `incorrect_candidate_refused` |
| Obtention effective | `obtain_produces_and_returns`, `obtain_register_exact`, `obtain_work_exact` |
| Refus sans modification de mémoire | `refusal_preserves_memory` |
| Handles et références | `History.realization`, `History.handle_transport`, `RegisterRealization.advance_position`, `RegisterRealization.injective`, `runSteps_old_read` |
| Lois locales indépendantes | `sourcePerform_exact`, `bridge` |
| Formation et lecture riches | `HistoricalFormation`, `HistoricalFormation.not_given`, `MaterialReading`, `RichOperation`, `sourceProduced` |
| Deux transports internes composés | `InternalStepAgreement`, `FollowedStages.engineTransport`, `FollowedStages.historicalTransport`, `FollowedStages.execution_exact` |
| Critère d'acceptation de toutes les réponses | `ReplyCriterion`, `FiniteResponseCriterion`, `Followed.satisfies`, `Certificate.satisfaction` |
| Toutes les interactions finies et leurs étapes internes | `FollowedStages`, `all_executed_determinations_followed`, `all_future_requests_exact`, `all_future_events_exact`, `all_future_reads_exact` |
| Admissions dans les deux sens | `admissions_forward`, `admissions_reflected`, `admission_received_return`, `admission_realized_return` |
| Mémoire entière et oubli | `agent_memory_factors_through_output`, `initial_profile_not_recoverable`, `forgotten_sources_same_future` |
| Paquet fermé | `certify`, `Prepared.certificate` |

La couche [Agents/Constitutive](../RelationalPerimeter/Agents/Constitutive/PublicInstance.lean)
est terminale : aucun module antérieur ne l’importe. Les rangs A10 à A16 et le
root A17 sont contrôlés par les deux vérificateurs de stratification.

```text
lake clean
lake build +RelationalPerimeter
lake build
bash scripts/verify.sh
pwsh -File scripts/verify.ps1
git diff --check
```

Les trois fichiers `Tests/ConstitutiveAgent*.lean` contiennent les constructions
positives et les petits contrôles de calculabilité. Le scénario public obtient
une cible absente, la réutilise sans nouvelle étape et distingue les refus. Ces
évaluations finies ne sont pas une campagne confirmatoire de complexité.

L'audit du commit `f6c6d2c051ae0886056d47cf5357253c137a1319` conclut
`AGENT TARGET REQUIRES CORRECTIONS` et `NO REGRESSION VERIFIED`. Les raccords
ci-dessus constituent la correction de ses sept constats ; leur vérification
locale est distincte d'un nouveau verdict indépendant.

[English version](constitutive-agent-and-persistence.en.md)
