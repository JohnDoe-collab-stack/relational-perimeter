# Constitution relationnelle calcul endogène et persistance de l’alignement

Nous avons construit un calcul qui produit sa décomposition opérationnelle,
puis un agent qui peut poursuivre ce calcul sous une exigence reçue sans
conserver le profil source dont il est parti. Les preuves suivent les
dépendances depuis la constitution des objets jusqu’aux réponses futures de
l’agent. Elles établissent ensemble un regroupement autorisé des obligations,
une perte effective de distinction dans la mémoire et la continuation correcte
du travail après cette perte.

La différence est importante pour l’alignement : nous ne vérifions pas seulement
que des messages respectent une règle. Nous démontrons que les productions,
les lectures autorisées et les actions futures restent conformes à un contrat
précis lorsque la mémoire utilisée pour agir ne permet plus de reconstruire
le choix initial. Cet alignement est celui de l’agent symbolique construit
ici, relativement à l’exigence définie plus bas.

## La constitution précède les lectures

Le cadre prend les relations et leurs témoins comme primitives constitutives.
Une occurrence n’est pas seulement une valeur : son identité dépend de sa
formation et de sa place dans une histoire composable. Un rôle constitutif
relationnel expose les dépendances auxquelles cette occurrence participe.

Les quatre fichiers initiaux distinguent notamment la réalisation du périmètre,
sa complétude intérieure et sa maximalité relative à un régime. Une continuation
peut être engendrée positivement sans pouvoir être incorporée à ce régime.
La génération, la réalisation, l’admission et la satisfaction d’une
spécification ne sont donc pas des synonymes.

Le carrier est le support formel équipé de la structure sur laquelle on travaille.
Cette structure n’est pas neutre. Dans l’exemple à quatre nœuds, des modèles
séparateurs conservent les données locales tout en perdant l’ordre ou le pont
composable entre positions adjacentes. Pour toute présentation, l’histoire
enracinée et composable permet de reconstruire l’ordre, l’adjacence et la
factorisation. La seule collection des valeurs locales ne remplace pas cette
constitution globale.

La couche computationnelle part de cette génération réelle. Elle constitue
ensuite des histoires dépendantes de rôles et leurs occurrences. Un profil
sélectionne une occurrence déjà constituée à chaque rôle. L’extensivité est la
lecture quantitative des profils ainsi obtenus, pas ce qui les constitue.
L’extension par ressources typées rend également visibles les entrées que
chaque producteur lit et la valeur qu’il produit depuis ces entrées.

Cette primitivité est interne à l’architecture du projet. Lean fournit la
métathéorie dans laquelle elle est formalisée ; le résultat n’est pas une
réduction de Lean ou de ZFC à cette architecture.

## Le calcul produit le statut opérationnel des alternatives

Une étape engendre deux occurrences distinctes. Cette distinction ne décide
pas encore qu’il faudra poursuivre deux obligations indépendantes. Dans la
famille publique, la recherche reconstruit une relation dirigée : ses candidats
infructueux sont réellement essayés, et la relation retenue est appliquée par
l’étape exécutée.

Cette action est définie sur des continuations arbitraires. Une preuve séparée
établit la préservation du critère d’acceptation. Le regroupement n’est donc
pas justifié en déclarant une alternative impossible ou en identifiant les
deux occurrences. Les témoins de viabilité, de distinction et de préservation
restent des obligations différentes.

La même récursion forme la décomposition de l’étape courante, puis continue
depuis l’état qu’elle a produit. Le résultat précédent fournit notamment la
graine et la provenance utilisées par la recherche suivante. La tête n’attend
pas une histoire future terminée pour décider sa décomposition.

L’instance maître fournit ces étapes, les rôles, le programme, la normalisation,
le régime d’obligations et le curseur de reprise depuis un résultat exécuté
commun. Les accords démontrent que les différentes interfaces portent bien
ce calcul, et non des constructions indépendantes simplement assemblées.

L’endogénéité désigne ici cette dépendance envers les productions réelles du
calcul. Elle ne signifie ni que le système invente ses primitives, ni que la
graine est informationnellement nouvelle. Dans l’instance publique, toutes les
étapes exécutées aboutissent au regroupement de leurs deux alternatives ; le
résultat ne prétend pas exhiber toutes les partitions opérationnelles possibles.

## Ce que nous prouvons sur la largeur exponentielle

Avec n rôles binaires, le carrier source contient exactement 2ⁿ profils.
Ces profils sont constitués avant leur portage comme obligations. L’application
`carry` envoie chacun d’eux vers une obligation du régime.

Pour tout problème de toute famille binaire formalisée et tout régime fini
surjectif sur son carrier, les deux directions sont prouvées :

```text
largeur opérationnelle = 2ⁿ
    si et seulement si carry est injective
```

L’injectivité signifie que deux profils distincts ne reçoivent jamais la même
obligation. Elle permet de construire un adressage séparé passant par le
régime lui-même : profil, obligation, puis adresse. Cet adressage n’est pas
une hypothèse indépendante ajoutée à l’injectivité.

Sur les mêmes profils, le régime identitaire conserve 2ⁿ obligations tandis
que le régime exécuté en porte une seule. Dans la famille publique,
n = input + 1. Les politiques de regroupement partiel ont une largeur 2ᵏ,
où k compte les rôles conservés séparément. Ces politiques sont des régimes
construits sur les mêmes rôles, pas de nouvelles exécutions de découverte.

La largeur un du régime exécuté ne vient pas du choix indépendant d’un type
singleton. La normalisation produit une cible pour chaque profil et une trace
indexée par sa source et sa cible. Le régime réalise l’image de ces sorties :
deux profils reçoivent la même obligation exactement lorsque leurs cibles
produites sont égales, ou, de façon équivalente, lorsque leurs traces les
codéterminent. La convergence des sorties donne ensuite la largeur un.

La conservation intégrale de la largeur extensive exponentielle est ainsi
caractérisée comme l’effet exact de la conservation indépendante de tous les
profils. Elle n’est pas une conséquence nécessaire de leur multiplicité :
une même multiplicité admet ici un régime exécuté et autorisé de largeur un,
sans égaliser les profils sources.

Le lemme général sur une surjection finie est un fait de cardinalité. Il reste
vrai lorsque les relations de la classe sont triviales. La contribution de
l’instance exécutée ne se réduit pas à ce lemme : elle construit et autorise
effectivement le regroupement depuis les actions relationnelles, puis le
raccorde au même carrier auquel s’applique le théorème de classe.

Ce résultat caractérise la largeur complète 2ⁿ. Il ne dit pas que tout régime
non injectif possède une largeur sous-exponentielle, ni que toute dépense en
temps ou en mémoire est exclue.

## La lecture quantitative ne remplace pas l’action

Le programme constitutif public contient exactement n instructions, avec n
atomes de code local retournés par l’exécution. Son interprétation reproduit
exactement la normalisation pour chaque profil et chaque donnée admise.
Il ne s’agit donc pas seulement d’un résumé plus court des 2ⁿ profils :
ce programme réalise leur transformation. Cette mesure compte les instructions
et les atomes locaux, pas les octets de tous leurs arguments ni le coût total
du calcul.

Une autre preuve précise ce que la projection étudiée par état et quantité
ne permet pas de retrouver. Le transport de l’instruction faisant autorité
et un transport de comparaison ont la même vue projetée et s’accordent sur
la continuation observée. Pourtant, leurs actions diffèrent sur une autre
continuation admissible. Leur action totale n’est donc pas reconstructible
depuis cette seule vue.

Dénombrer les profils, lire une largeur ou observer une sortie ne suffit pas
à connaître ce que le calcul fera sur toute continuation. Cette limite porte
sur la projection formalisée, pas sur toutes les représentations imaginables.
Les garanties futures de l’agent exigent les accords d’action et de lecture
démontrés plus bas ; elles ne se déduisent pas de la seule largeur un.

## Le regroupement et l’oubli sont deux résultats distincts

Regrouper deux profils en une obligation ne suffit pas à les oublier. Un
système pourrait conserver les deux profils dans une archive et les retrouver
à tout moment. Nous distinguons donc l’interface scientifique, qui conserve
les témoins historiques, de la mémoire utilisée pour poursuivre le calcul.

La mémoire complète de l’agent contient exactement trois éléments : l’exigence
reçue, le moteur vivant et le registre des cibles produites. La session ne
contient que cette mémoire. Le profil source initial et son code de sélection
ne sont pas des champs cachés de la session.

Deux profils sources explicitement construits et prouvés distincts donnent
la même mémoire complète. Il n’existe donc pas de fonction de cette mémoire
vers le profil initial qui reconstruise correctement toutes les initialisations.
Ce n’est pas seulement l’absence d’une fonction de décodage dans l’API : son
impossibilité uniforme est démontrée.

Les profils ne deviennent pas égaux dans l’histoire qui les constitue.
Leur distinction reste établie dans l’interface scientifique. C’est la mémoire
de reprise qui ne permet plus de savoir lequel a été utilisé. La perte porte
sur ce choix initial, non sur toutes les distinctions ou toute la provenance
encore nécessaire au calcul.

Les transports exacts utilisés ailleurs possèdent leurs deux lois de retour.
Ils ne rendent pas réversible cette projection vers la mémoire de reprise.
L’extension d’un support, quant à elle, transporte injectivement ses anciennes
références en préservant leurs lectures. Ces trois opérations ont des fonctions
différentes : correspondance exacte, conservation dans un support étendu et
oubli sous un contrat futur.

## L’exigence reçue gouverne une interaction effective

L’exigence concrète demande de poursuivre le moteur autorisé et de ne restituer
que les valeurs de productions réelles pour des variables appartenant au
périmètre reçu. Ce périmètre fournit des droits de lecture, pas des réponses
attendues. Il ne choisit pas non plus les variables de la découverte.

L’agent peut avancer le moteur, consulter une cible existante, produire les
étapes nécessaires à une cible absente ou vérifier une valeur proposée.
Chaque réponse autorisée possède un témoin qui relie la permission reçue,
l’occurrence réellement présente et la valeur lue. Une variable interdite,
une cible absente et une valeur incorrecte justifient des refus distincts.
Un refus laisse la mémoire entière inchangée.

Le contrat n’est pas satisfait par un agent qui refuse tout. Pour une lecture
permise, `obtain` produit effectivement les étapes manquantes et répond.
Si le registre contient r cibles et que l’adresse h manque, il produit
exactement h + 1 − r étapes. Si la cible existe déjà, il n’en produit aucune.
La taille de ce registre n’est pas la largeur des obligations indépendantes.

Voici un calcul vérifié depuis `publicAgent 0 [0] [false]`. Les adresses
commencent à zéro : 0 désigne la première cible, 2 la troisième. Seule la
variable 0 est autorisée. Le registre contient initialement une cible.

| Demande | Étapes nouvelles | Résultat |
| --- | --- | --- |
| Lire la variable 0 de la cible 0 | 0 | Réponse `true` |
| Obtenir la variable 0 de la cible 2 | 2 | Production de deux étapes et réponse `true` |
| Relire la variable 0 de la cible 2 | 0 | Même réponse, sans nouvelle étape |
| Lire la cible 200 | 0 | Refus pour cible absente |
| Lire la variable 1 de la cible 0 | 0 | Refus pour variable hors périmètre |
| Avancer d’une étape | 1 | Une production supplémentaire |

Le registre final contient quatre cibles. Leur contexte d’acceptation et leur
origine sont conservés. Une lecture booléenne dans l’une de ces cibles n’est
pas présentée comme une résolution globale de SAT. Ce petit calcul illustre
l’API ; il ne remplace pas les preuves générales.

## La continuation après l’oubli est démontrée

L’interface scientifique lit un support riche formé par les producteurs et
leurs références typées. La session agit depuis sa mémoire de reprise.
Les preuves relient ces deux parcours : elles portent séparément sur l’état
suivant, les événements, les lectures et les admissions.

Ces accords valent pour toute suite finie de demandes, quelle que soit sa
longueur. Ils suivent aussi chacune des étapes internes nécessaires à une
demande, et pas seulement les réponses visibles. L’ajout d’une production
conserve les anciennes lectures et transporte leurs références. Les admissions
passent dans les deux sens avec deux lois de retour sur leurs témoins.

La réponse courante dépend de la mémoire et de la demande courantes, sans
paramètre de demandes futures. Deux suites ayant la même tête produisent la
même tête d’interaction. L’exigence reste identique après toute suite de demandes,
et sa réalisation continue à lui correspondre exactement.

Enfin, les deux profils oubliés donnent les mêmes mémoires, événements et
réponses pour les mêmes demandes futures. L’agent continue donc à remplir le
contrat sans qu’il faille réintroduire le profil perdu ou consulter l’archive
scientifique pour agir.

## Ce que ce résultat apporte à l’alignement

L’alignement établi ici est la conformité persistante à cette exigence
formelle. Conserver un champ contenant la règle ne suffirait pas à le démontrer.
Les preuves doivent aussi établir que les réponses lisent les bonnes
productions, que les permissions sont respectées, que les reprises exécutent
le moteur réel et que tous ces accords survivent à la perte du choix initial.

L’architecture relie ces garanties depuis leurs dépendances constitutives.
Elle ne se limite donc pas à examiner les messages d’un calcul laissé opaque :
elle suit ce qui produit les réponses et ce qui permet de continuer après une
transformation de la mémoire. La vérification Lean établit ces accords ; elle
n’est pas un surveillant externe qu’il faudrait appeler à chaque interaction.

Nous obtenons ainsi une continuation correcte après une perte démontrée de
distinction, relativement à des droits et à des actions explicitement définis.
Une information peut cesser d’être récupérable sans que les garanties promises
au futur soient perdues. C’est le lien entre constitution, regroupement,
mémoire et continuation qui donne sa portée au résultat pour l’alignement.

Le contrat est reçu de l’extérieur. Le calcul ne produit pas lui-même une
norme morale ni l’interprétation de toute intention humaine. L’instance est
un agent symbolique, pas un modèle de langage entraîné. Les preuves ne
constituent pas une garantie générale sur une IA déployée, une borne physique
de mémoire ou un théorème de coût total. Elles ne supposent pas non plus que
toutes les autres architectures seraient incapables de telles garanties.

## Preuves et état de validation

Les résultats sont accessibles depuis `import RelationalPerimeter`.
Les déclarations suivantes permettent de retrouver leurs énoncés exacts.
Dans les lignes relatives à l’agent, le namespace est `ConstitutiveSearch.Agent`.
Les déclarations de l’instance maître appartiennent à
`ConstitutiveSearch.EndogenousDecomposition.UnifiedMaster`.

| Résultat | Source et déclarations |
| --- | --- |
| Production depuis des références typées et maintien des lectures | [ConstructedSupport](../RelationalPerimeter/Constitution/Resources/ConstructedSupport.lean), `produced_value`, `produced_preserves`, `Support.Extension.compose` |
| Même instance exécutée pour les rôles, le régime et la reprise | [UnifiedPublicCertificate](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean), `UnifiedMaster.publicInstance`, `Instance.audited_execution_exact`, `Instance.all_heads_exact` |
| Largeurs 2ⁿ, 2ᵏ et un sur les mêmes rôles | [UnifiedPublicCertificate](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean), `Instance.source_width`, `Instance.partial_width`, `Instance.executed_width` |
| Théorème binaire appliqué au régime exécuté sans adaptation de carrier | [UnifiedPublicCertificate](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean), `class_carrier_exact`, `class_iff_on_master_carrier`, `class_iff_on_executed_regime` |
| Regroupement exact et paire de profils distincts | [UnifiedPublicCertificate](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean), `Instance.carry_fibres`, `Instance.coDetermination_fibres`, `Instance.distinctPair` |
| Programme de n instructions et interprétation exacte | [ConstitutiveNormalizerSuccinctness](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ConstitutiveNormalizerSuccinctness.lean), `public_constitutive_program_instructionCount_exact`, `public_constitutive_program_codeSize_exact`, `public_constitutive_normalizer_interpreter_exact` |
| Action totale non reconstructible depuis la vue par état et quantité | [ExtensionalOperationalStability](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ExtensionalOperationalStability.lean), `ExecutedExtensionalSeparator.authoritative_instruction_projection_collision`, `ExecutedExtensionalSeparator.authoritative_instruction_action_not_factors_on_executed_system` |
| Cibles et valeurs réellement produites | [ProducedEvidence](../RelationalPerimeter/Agents/Constitutive/ProducedEvidence.lean), `TargetOrigin`, `initialTargets`, `resumedTarget`; [Agreement](../RelationalPerimeter/Agents/Constitutive/Agreement.lean), `executed_step_register_exact` |
| Acceptation dérivée de l'origine, puis consommée par le contrat fini | [ProducedEvidence](../RelationalPerimeter/Agents/Constitutive/ProducedEvidence.lean), `TargetOrigin.accepted`; [Agreement](../RelationalPerimeter/Agents/Constitutive/Agreement.lean), `ReplyCriterion`; [Persistence](../RelationalPerimeter/Agents/Constitutive/Persistence.lean), `Followed.satisfies`, `Certificate.satisfaction` |
| Réponses correctes, obtention effective et refus | [Agreement](../RelationalPerimeter/Agents/Constitutive/Agreement.lean), `candidate_authorization_exact`, `obtain_produces_and_returns`, `obtain_work_exact`, `refusal_preserves_memory` |
| Références historiques et lectures du registre | [State](../RelationalPerimeter/Agents/Constitutive/State.lean), `History.realization`, `History.handle_transport`, `RegisterRealization.materialRegister_exact`, `RegisterRealization.advance_position` |
| Formation et lecture du support riche | [State](../RelationalPerimeter/Agents/Constitutive/State.lean), `HistoricalFormation`, `MaterialReading`; [Agreement](../RelationalPerimeter/Agents/Constitutive/Agreement.lean), `RichOperation`, `sourceProduced` |
| Tête produite sans futur et spécification riche indépendante | [Agreement](../RelationalPerimeter/Agents/Constitutive/Agreement.lean), `head_production_entire_exact`, `head_horizon_independent`, `sourcePerform_exact`, `bridge` |
| Toutes les interactions finies et leurs étapes internes | [Persistence](../RelationalPerimeter/Agents/Constitutive/Persistence.lean), `all_executed_determinations_followed`, `all_future_requests_exact`, `all_future_events_exact`, `all_future_reads_exact` |
| Deux extensions composées sur les supports effectivement suivis | [Persistence](../RelationalPerimeter/Agents/Constitutive/Persistence.lean), `InternalStepAgreement`, `FollowedStages.engineTransport`, `FollowedStages.historicalTransport`, `FollowedStages.execution_exact` |
| Admissions transportées et exigence persistante | [Agreement](../RelationalPerimeter/Agents/Constitutive/Agreement.lean), `admission_received_return`, `admission_realized_return`; [Persistence](../RelationalPerimeter/Agents/Constitutive/Persistence.lean), `admissions_forward`, `admissions_reflected`, `requirement_persists` |
| Égalité des mémoires complètes et impossibilité de décodage uniforme | [State](../RelationalPerimeter/Agents/Constitutive/State.lean), `agent_memory_factors_through_output`; [Persistence](../RelationalPerimeter/Agents/Constitutive/Persistence.lean), `initial_memories_equal`, `initial_profile_not_recoverable`, `forgotten_sources_same_future` |
| Instance d’agent et certificat fermé | [PublicInstance](../RelationalPerimeter/Agents/Constitutive/PublicInstance.lean), `publicAgent`, `Prepared.certificate`, `publicSession`; [Persistence](../RelationalPerimeter/Agents/Constitutive/Persistence.lean), `certify` |
| Code reçu, décodage et mémoire initiale raccordés | [PublicInstance](../RelationalPerimeter/Agents/Constitutive/PublicInstance.lean), `InitializationCertificate`, `Prepared.prepare_exact`, `initialize_invalid_selection`, `initialize_wrong_length` |

Le résultat causal de largeur exponentielle a reçu le verdict indépendant
`EXACT TARGET ESTABLISHED` sur le commit
[4e0febf032821882069e7cfefd7e631fc8461d95](https://github.com/JohnDoe-collab-stack/relational-perimeter/commit/4e0febf032821882069e7cfefd7e631fc8461d95).
Ce verdict appartient à cette révision : il ne valide pas automatiquement
les extensions ultérieures.

La première version de l'agent a été auditée au commit
[f6c6d2c051ae0886056d47cf5357253c137a1319](https://github.com/JohnDoe-collab-stack/relational-perimeter/commit/f6c6d2c051ae0886056d47cf5357253c137a1319).
Cet audit a conclu `AGENT TARGET REQUIRES CORRECTIONS` et
`NO REGRESSION VERIFIED`. Les raccords d'initialisation, d'origine, de lecture
riche, de suivi interne et de critère fini cités ici sont les corrections
apportées à ses constats. Les contrôles compilés suivent désormais les wrappers
de session et leurs auxiliaires ; les refus attendus exigent les diagnostics
Lean structurés aux sites figés. Ils ne constituent ni une analyse générale du
tas ni une preuve de coût total. La vérification locale de la correction ne
doit pas être confondue avec un nouveau verdict indépendant.

## Documents complémentaires et reproduction

La [présentation des quatre fichiers initiaux](relations-primitives-constitution-perimetre.fr.md)
expose le périmètre et la méthode. La [conclusion sur la largeur exponentielle](conclusion-largeur-exponentielle-conservation-identites.fr.md)
conserve la cible scientifique et sa portée exacte. La [continuation après normalisation](continuation-et-oubli-des-profils.fr.md)
et la [documentation de l’agent](agent-constitutif-et-persistance.fr.md)
détaillent les contrats et leurs interfaces.

Depuis la racine du dépôt, avec Lean 4.33.1 et Python 3 :

```text
lake clean
lake build +RelationalPerimeter
lake build
bash scripts/verify.sh
pwsh -NoProfile -File scripts/verify.ps1
git diff --check
```

Le [scénario d’interaction](../Tests/ConstitutiveAgentExecution.lean) présenté
plus haut peut être relu et exécuté séparément. Les
[preuves sur la mémoire et les futures interactions](../Tests/ConstitutiveAgentPersistence.lean)
construisent les témoins publics de distinction, d’oubli et de continuation.
