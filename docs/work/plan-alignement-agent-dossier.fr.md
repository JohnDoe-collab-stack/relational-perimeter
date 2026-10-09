# Plan — Un agent qui accomplit une tâche sous contrat après oubli

**Branche de travail :** `codex/ai-alignment-under-contract`.

**Révision du plan :** 9 octobre 2026, après la
[relecture du code et du premier raccordement](reverification-plan-alignement.fr.md).

**Statut :** plan de chantier corrigé. La constitution, le regroupement, la
continuation depuis le présent et plusieurs garanties d'oubli sont déjà prouvés.
Le premier raccordement avec Qwen est réalisé et vérifié. Les lots ci-dessous
précisent les constructions à réutiliser, les lois à fermer pour une nouvelle
instance et les garanties supplémentaires à démontrer. Leur rédaction ne
change ni les preuves, ni les contrats, ni les résultats de référence.

## Cible

Construire un agent local qui réalise une tâche documentaire utile, conserve
le contrat reçu et peut continuer jusqu'à l'accomplissement après des oublis
autorisés. Ses opérations effectives, ses réponses et le livrable doivent
appartenir à la même chaîne de constitution et de preuve.

Le cas proposé est un **agent qui construit un dossier sourcé à partir de
documents reçus**. Il constitue des occurrences d'information, établit leurs
relations, produit des éléments justifiés et forme le dossier demandé. Le
modèle propose des recherches, des rapprochements et des constructions ; leur
incorporation consomme les permissions, les ressources et les préservations
effectivement disponibles.

Cette application doit être validée par un premier raccord complet entre une
source reçue, une occurrence constituée, une action produite, sa préservation
et un élément effectivement réalisé. Les lots 2 et 3 commencent par ce cas.
La lecture booléenne de l'agent actuel délimite son interface ; elle ne suffit
pas à réaliser ce raccord documentaire et ne délimite pas toute la théorie.

La première classe de dossiers comprendra des extraits précisément référencés,
des données typées et des déductions par des règles exécutables explicites.
Le contenu publié sera rendu depuis ces éléments constitués. Les propositions
de rédaction libre nécessiteront un critère de validation sémantique propre
avant de recevoir la même garantie. Une provenance valide établit un rapport
aux sources ; la vérité des sources sur le monde demande son propre critère.

Le résultat visé est la conjonction de trois obligations :

1. Toute exécution admise respecte le contrat, quelles que soient les propositions
   du modèle et les remises à zéro de son contexte.
2. La mémoire conservée suffit aux futurs déclarés, avec leurs admissions,
   événements, lectures et possibilités d'accomplissement.
3. Pour une tâche admissible de la classe définie, une procédure effectivement
   construite atteint un état d'accomplissement et produit le livrable correspondant.

Ces obligations ont des énoncés distincts et un raccord explicite. Le chantier
vise la troisième même lorsqu'une politique propose toujours des erreurs ou
aucune opération : il ajoute donc un ordonnanceur qui porte le progrès.
L'accomplissement positif d'une demande permise est déjà acquis dans l'agent
actuel ; cette garantie globale constitue une extension précise.

## Point de départ vérifié

Le chantier part de `main`, révision
`b71904ab3b1cabb18faec791a690fa87b434e00e`.

| Résultat déjà fermé | Évidence et portée |
| --- | --- |
| Constitution, recherche, action et continuation | [MasterResourceExecution.lean](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/MasterResourceExecution.lean) et [certificat du maître](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean) : ressources réellement produites et consommées par la même exécution |
| Regroupement issu des productions | [ExecutedCausalNormalization.lean](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ExecutedCausalNormalization.lean) : autorisation, préservation et lois de retour ; profils sources distincts portés ensemble |
| Exécution depuis le présent retenu | [LiveResourceContinuation.lean](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/LiveResourceContinuation.lean) et [ConstitutiveLiveExecution.lean](../../RelationalPerimeter/Computation/Machine/ConstitutiveLiveExecution.lean) : producteurs concrets et accords avec leurs réalisations riches |
| Futurs exacts et oubli des profils de l'agent | [Persistence.lean](../../RelationalPerimeter/Agents/Constitutive/Persistence.lean) : toutes les suites finies de requêtes du langage déclaré, admissions dans les deux sens, événements et lectures |
| Minimalité comportementale du noyau machine | [ReducedLiveMinimality.lean](../../RelationalPerimeter/Computation/Machine/ReducedLiveMinimality.lean) : à scope fixé, sur les mémoires cohérentes, égalité de projection si et seulement si égalité de tous les futurs |
| Exactitude du runtime combiné avec SAT | [MasterContract.lean](../../RelationalPerimeter/Computation/Machine/MasterContract.lean) : requêtes du noyau, routages configurés et lectures du problème ; la frontière SAT reçue est conservée |
| Composition avec tout proposeur adaptatif | [ModelLoop.lean](../../Tests/LocalAlignment/ModelLoop.lean), `certifyRun` et `all_adaptive_requirements` |
| Conservation des anciennes lectures | `all_adaptive_old_reads` dans le même module |
| Accomplissement positif d'une demande `obtain` permise | `permitted_obtain_answer` dans le même module et [Agreement.lean](../../RelationalPerimeter/Agents/Constitutive/Agreement.lean) : production des étapes nécessaires et réponse autorisée |
| Irrécupérabilité dans l'état composé | `initial_profile_not_recoverable_combined` : aucun récupérateur uniforme du profil initial, à contexte initial fixé |
| Transport des entrées brutes vers le producteur certifié | [Kernel.lean](../../Tests/LocalAlignment/Kernel.lean) |
| Exécution avec un modèle réel | [Résumé confirmatoire](../../apps/local-alignment/evidence/summary.json) : 12 appels à Qwen, 4 effacements du contexte, 8 étapes produites, 7 réponses autorisées, rejeu exact |
| Vérifications du dépôt | [Bilan des contrôles](../../apps/local-alignment/evidence/verification.json) : 246 fichiers Lean, 20 868 constantes examinées, 23 fixtures de refus attendu |

Le [rapport du premier raccordement](alignement-ia-locale-resultats.fr.md)
donne les énoncés, les résultats et leur portée. Le
[protocole figé](../../apps/local-alignment/evidence/protocol.json) identifie
l'arbre effectivement utilisé. La nouvelle relecture a confirmé ses 251
empreintes, relancé la gate complète et rejoué exactement les douze échanges.
Le commit de livraison fixe la révision de référence du raccordement et de ces
documents de chantier. L'enregistrement de sa nouvelle évidence scientifique
reste à effectuer sur cette révision.

### Trois niveaux reliés, avec leurs contrats propres

| Niveau | Instance et langage |
| --- | --- |
| Maître constitutif | `UnifiedMaster.publicInstance` : une exécution de ressources dont sont dérivés rôles, normalisation, obligations et point de continuation |
| Machine avec routage SAT | `MasterMachine.receive` : maître, scope, formule et contextes SAT reçus ; opérations du noyau, routages et lectures entrelacés |
| Agent relié à Qwen | `Agent.Memory`, `ModelLoop` et `Kernel` : contrat de restitution, moteur vivant et registre ; `advance`, `inspect`, `obtain`, `propose` |

Les deux applications consomment des constructions du même maître. Le conducteur
Qwen actuel utilise l'agent constitutif. La minimalité du noyau, l'exactitude
du runtime SAT combiné et l'oubli des profils de l'agent gardent leurs domaines
et leurs hypothèses propres. Le raccord documentaire doit annoncer les
interfaces qu'il consomme et fermer ses lois sur cette instance.

## 1. Figer le premier raccordement

**But :** disposer d'une référence reproductible avant d'étendre la tâche.

La relecture de la chaîne, l'accord des empreintes, la gate complète et le
rejeu du premier raccordement ont été exécutés. Ce lot doit fixer leur référence
dans l'historique et préparer leur enregistrement scientifique.

- Relire ensemble le client formel, le noyau de transport, le conducteur Qwen,
  les reçus et le rapport ; vérifier que les garanties décrites sont celles
  des énoncés complets.
- Vérifier les empreintes de l'arbre contre le protocole confirmatoire et
  conserver les deux expériences déjà effectuées avec leurs identités propres.
- Constituer le commit de référence lorsque ce lot est demandé. La publication
  de la branche suit l'instruction de publication correspondante.
- Préparer les entrées scientifiques nouvelles avec leur passage canonique,
  leur portée et leurs références. Figer leur évidence sur une révision existante,
  conformément à la [procédure scientifique](../methode-de-travail-scientifique.fr.md).
- Garder les statuts de revue attachés aux rapports et révisions effectivement
  disponibles. Le registre existant conserve ses évidences propres.

**Livrable :** une révision de référence, son manifeste et une fiche des garanties
du premier raccordement.

**Critère de sortie :** les preuves, le conducteur, les résultats livrés et les
affirmations canoniques désignent le même arbre vérifiable. Le document de plan
reste un document de chantier.

## 2. Définir la tâche documentaire et son contrat

**But :** fixer ce que l'agent doit effectivement accomplir avant de choisir
les structures qui permettront de le prouver.

Définir une première classe finie de dossiers, assez riche pour former un
livrable utile : sections demandées, informations attendues, sources admissibles,
relations de justification et règles de déduction. Constituer une instance
concrète comportant plusieurs sources, des dépendances entre éléments et des
occurrences distinctes qui portent une même valeur.

Avant de figer cette classe, éprouver une action documentaire entière avec les
producteurs du lot 3. Documenter ce que les interfaces existantes réalisent,
l'extension requise et ses lois. Une traduction vers une variable booléenne
doit justifier le sens conservé par cette traduction. Si ce cas ne ferme pas
ses obligations, annoncer le défaut du raccord et reprendre la spécification
de l'application proposée sans affaiblir le contrat ni le critère reçu.

| Partie du contrat | Définition à produire |
| --- | --- |
| Entrées | Documents reçus, versions fixées, demande humaine et ressources de départ |
| Permissions | Lectures, transformations et restitutions permises, avec leur portée |
| Contenu publiable | Témoins de source et règles de construction exigés pour chaque élément |
| Effets | Fichiers que l'agent peut créer ou modifier, et opérations disponibles |
| Accomplissement | Sections et obligations satisfaites, cohérence du dossier et livrable effectivement réalisé |
| Admissibilité | Conditions positives qui rendent la tâche réalisable avec les ressources reçues |
| Futurs | Requêtes, événements, lectures, progrès et accomplissement couverts après une projection mémoire |
| Reprises durables | Encodage, sauvegarde et chargement de l'état retenu ; conditions de validité du checkpoint et réponse aux erreurs |
| Évolution | Conditions de changement de contrat et nouvelle justification de la mémoire nécessaire |

Écrire le critère d'accomplissement indépendamment du proposeur et du programme
qui construira le dossier. Une tâche indisponible ou contradictoire doit recevoir
un diagnostic défini ; elle ne doit pas être annoncée accomplie.

L'admissibilité doit fournir des ressources permettant de construire une solution.
Elle ne doit pas recevoir implicitement un dossier déjà achevé. Les effets et
leurs conditions de succès sont spécifiés ici ; le lot 6 réalise cette interface
et ferme son accord avec l'exécution.

**Livrable :** spécification du cas d'usage, vocabulaire des actions, contrat de
futurs et critère d'accomplissement, accompagnés d'une instance concrète.

**Critère de sortie :** le lecteur peut déterminer ce qui compte comme réponse
permise, tâche admissible et dossier achevé sans connaître l'algorithme.

## 3. Constituer les informations et les actions dans la chaîne existante

**But :** porter le traitement documentaire par des ressources réellement
produites et consommées.

**Appui existant :** les producteurs constitutifs, l'action et sa préservation
séparée, le regroupement autorisé et la continuation sont construits dans la
chaîne du maître. Ce lot ferme leur raccord à la nouvelle tâche.

Construire les relations de lecture, d'extraction, de justification et de
dépendance. Une occurrence d'information reçoit son identité de sa formation :
source, position, version, histoire et opération productrice. L'égalité de
contenu ne suffit pas à transférer ses permissions ou son origine.

Reconstituer pour chaque opération la chaîne entière :

```text
sources, demande et permissions reçues
  -> relations primitives et témoins positifs
  -> occurrences, histoires et contextes constitués
  -> recherche effectivement exécutée
  -> action produite et preuve séparée de préservation
  -> incorporation et obligations produites
  -> continuation, mémoire et observations
  -> contenu et livrable réalisés
```

- Construire l'adaptateur qui relie les données documentaires à l'instance maître
  et aux producteurs pertinents. Fermer l'accord de lecture des sources,
  la formation des occurrences, la consommation par l'action, sa préservation
  sémantique et la correspondance avec l'élément réalisé.
- Identifier les étapes que l'instance actuelle porte effectivement et celles
  qui demandent une extension formelle. Cartographier leurs consommateurs avant
  toute revendication de raccordement complet.
- Pour chaque passage, consigner formation, exécution, consommation dans la
  preuve et transport. Un champ de provenance doit correspondre à la production
  qui a formé la donnée utilisée.
- Partager le résultat réellement produit entre état suivant, justification,
  trace et restitution ; contrôler cette consommation jusque dans le code généré.
- Lorsqu'un regroupement d'obligations est permis par une relation produite,
  consommer les autorisations et lois de retour de la chaîne. Constituer les
  relations documentaires qui permettent de traiter ces obligations ensemble,
  avec la préservation de leur critère et la conservation des identités sources.
  Une similarité de texte ne constitue pas ce témoin.
- Séparer réalisation, admission, satisfaction du contrat et adéquation du régime.

**Livrable :** types exécutables, producteurs documentaires, actions, préservations
et adaptateur concret, avec une carte de leurs dépendances.

**Critère de sortie :** chaque élément du dossier se rattache à une occurrence
formée et chaque incorporation à ses ressources effectives. Les nouvelles
lois d'accord sont fermées sur la même instance exécutée. Les nouvelles
déclarations Lean et leurs audits passent sans axiome.

## 4. Construire la continuation qui accomplit la tâche

**But :** garantir un progrès positif même lorsque le modèle propose des erreurs
ou ne choisit pas une opération utile.

**Appui existant :** `obtain` produit les étapes nécessaires et répond pour une
demande permise. Le moteur reprend depuis son présent, et la composition
adaptative respecte le contrat pour toute politique. Une politique qui choisit
toujours `none` laisse toutefois la mémoire machine inchangée sur toute suite finie
de signaux. La terminaison d'un dossier malgré cette politique est l'obligation
supplémentaire de ce lot.

Former les obligations du dossier à partir de la demande et des relations
constituées. Construire une procédure de continuation qui choisit une obligation
réalisable, consomme ses ressources et produit un progrès vérifiable. Les choix
utiles du modèle peuvent participer à cette construction et à son ordonnancement.

Rendre leur contribution observable : quelle proposition acceptée modifie la
recherche, les relations constituées ou l'ordre des productions ? Cette
contribution doit consommer ses justifications. La preuve de conformité
quantifie sur toute politique ; elle ne demande pas que le modèle soit
indispensable à la continuation.

Prévoir explicitement le cas où sa proposition est invalide, redondante, absente
ou valide sans faire progresser la tâche. Des lectures autorisées répétées peuvent
laisser la mémoire et le travail restant inchangés. La machine doit disposer
d'une continuation autorisée qui traite une obligation encore ouverte. Un délai
d'inférence dépassé est représenté par une absence de proposition ; la définition
de la progression prend ce cas en compte.

**Obligation de progrès borné :** depuis tout état atteignable où la tâche reçue
est admissible et inachevée, construire une borne positive et finie à partir du
présent retenu, indépendante des prochains choix du modèle. Pour toute politique,
dans cette borne de tours contrôlés et sous les conditions d'environnement
déclarées, la procédure exécutée atteint l'accomplissement ou un état dont la
mesure bien fondée du travail restant est strictement inférieure à celle du
départ. Cette obligation couvre aussi une politique qui répète exclusivement
des opérations valides sans progrès.

La preuve doit raccorder cette borne à l'ordonnanceur réellement exécuté et
composer les diminutions pour établir la terminaison. Si l'ordonnanceur utilise
un compteur de tours, celui-ci appartient au présent machine et à son accord
de projection ; l'effacement du contexte du modèle ne réinitialise pas ce
compteur. Une diminution lors des seuls progrès, sans borne d'attente entre
eux, ne ferme pas cette obligation.

Déterminer l'accomplissement relativement à un dossier et à sa version : quelles
occurrences et quelles relations constituent exactement le tout demandé ? La
procédure de cette tâche atteint son terme ; la machine peut ensuite produire
d'autres occurrences et de nouveaux dossiers sous les contrats correspondants.
La complétude du dossier accompli doit rester compatible avec cette continuation.
Une extension reçoit son statut propre et ses témoins. Le périmètre exact,
la continuation positive au-delà et les obstructions du régime circulaire
sont déjà formalisés dans [StrongPerimetralTurning.lean](../../StrongPerimetralTurning.lean).
Les appliquer au dossier demande une instance de `CircularPresentation` :
compatibilité, jonction finale, frontières séparées et témoins d'obstruction,
puis réalisation exacte entre positions et occurrences. L'achèvement d'un
fichier ne fournit pas à lui seul ces données. Si cette structure est revendiquée
pour l'application, fermer chacune de ses obligations.

| Preuve à construire | Quantification et conclusion |
| --- | --- |
| Conformité des incorporations | Toute proposition du modèle, sur tout état atteignable, conduit à une action permise ou à un refus justifié |
| Existence d'un prochain progrès | Toute tâche admissible inachevée possède une continuation positivement construite qui fait avancer une obligation |
| Progrès de la procédure réelle | La transition exécutée consomme cette continuation, y compris après une proposition inutile ou absente |
| Progrès en un nombre borné de tours | Depuis tout état atteignable admissible et inachevé, une borne positive construite depuis le présent garantit, pour toute politique, l'accomplissement ou une diminution stricte de la mesure, même avec des propositions valides sans progrès |
| Terminaison | La composition des progrès bornés et la mesure bien fondée garantissent que la procédure exécutée atteint l'accomplissement sur la classe annoncée |
| Correction finale | L'état terminal et le livrable réalisé satisfont le critère reçu, défini indépendamment de la procédure |

Déclarer les hypothèses d'entrée, la disponibilité des ressources et les conditions
de réponse de l'environnement. Une borne de transitions contrôlées et une borne
de temps physique sont des résultats distincts. La terminaison de la procédure
ne sera pas conditionnée à une bonne volonté implicite du modèle.

**Livrable :** ordonnanceur exécuté depuis les ressources du présent, témoins de
progrès borné, mesure de terminaison et certificat d'accomplissement pour le
critère indépendant de la classe concrète.

**Critère de sortie :** toute politique, y compris celle qui propose
systématiquement des opérations incorrectes, aucune opération ou des lectures
valides sans progrès, laisse la procédure réaliser une tâche admissible sous
les conditions d'environnement explicitement démontrées ou reçues. La borne
de tours et sa consommation effective sont démontrées.

## 5. Déterminer la mémoire du présent et les oublis autorisés

**But :** conserver exactement les distinctions nécessaires aux futurs du dossier,
avec leurs permissions et leurs possibilités de progrès.

**Appui existant :** exécuteurs réduits concrets, accords de tous les futurs
déclarés, oubli irréversible des profils et minimalité comportementale du noyau
à scope fixé sur les mémoires cohérentes. L'agent documentaire doit fermer
ses propres lois pour son langage de futurs, ses ressources et ses effets.

Étendre la mémoire riche de référence, la projection vers le présent retenu
et l'exécuteur réduit avec les constructions documentaires. La mémoire retient
les ressources nécessaires aux prochaines actions, aux obligations, aux origines
utiles et aux observations couvertes par le contrat. Fermer ensemble les lois
de continuation du lot 4 et les lois de projection de ce lot.

- Démontrer l'accord riche/réduit sur toutes les suites finies du langage de
  futurs : états projetés, admissions dans les deux sens, événements et lectures.
- Inclure les événements de production et le critère d'accomplissement dans
  cet accord ; le progrès doit survivre à la projection. Conserver la mesure
  de terminaison et les ressources qui garantissent la borne de tours du lot 4,
  avec le compteur éventuel de l'ordonnanceur et ses lois d'accord.
- Construire, sur des états effectivement obtenus, une distinction oubliée et
  établir son irrécupérabilité depuis l'état retenu dans la portée annoncée.
- Inventorier les accès qui permettraient de reconstituer ce qui est annoncé
  oublié : archives, chemins de relecture, outils ou données indirectement
  accessibles. Ces accès appartiennent à la définition des futurs concernés.
- Construire des séparateurs montrant quelles distinctions le contrat oblige
  à garder. Pour revendiquer la minimalité de la mémoire documentaire, préciser
  le domaine cohérent et fermer sa preuve ; celle du noyau existant ne se
  transfère pas automatiquement au registre ou au runtime SAT combiné.
- Distinguer l'effacement du contexte du modèle, l'oubli irréversible des profils,
  la projection des supports historiques et la reprise après arrêt du processus.
  Le premier raccordement efface les anciens messages du modèle et conserve
  la mémoire du noyau vivant. Son rejeu réexécute les requêtes depuis le boot.
- Pour la reprise durable, définir une sauvegarde de l'état retenu, son chargement
  et leurs lois de retour ; démontrer l'accord des futurs depuis cet état chargé,
  avec les ressources accessibles au processus redémarré.
- Si le contrat s'élargit, déterminer à nouveau les ressources requises ; l'accord
  démontré pour un contrat fixé ne vaut pas automatiquement pour le contrat élargi.

Un support historique supprimé n'est pas nécessairement une histoire devenue
irrécupérable. [MasterContinuationFeasibility.lean](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/MasterContinuationFeasibility.lean)
reconstruit les préfixes canoniques sous le contrat fort de lectures de profondeur
et de provenance. Le cas d'oubli documentaire doit spécifier la distinction
perdue et prouver sa perte depuis l'état retenu dans son contrat propre.

**Livrable :** projection exécutée, accord de tous les futurs, cas construit
d'oubli, séparateurs des distinctions nécessaires et lois de reprise depuis
un checkpoint valide.

**Critère de sortie :** après les oublis autorisés, la machine peut poursuivre et
achever la tâche depuis les seules ressources retenues, dans le contrat déclaré.
Les affirmations sur les octets, le coût ou l'énergie gardent leurs mesures propres.

## 6. Raccorder les preuves au livrable et aux effets réels

**But :** obtenir un dossier effectivement écrit par l'agent local.

**Appui existant :** transport des propositions brutes, invocation du producteur
certifié, sorties du noyau, effacements du contexte de Qwen et rejeu exact.
Les nouveaux effets documentaires et la sauvegarde/reprise sont les réalisations
à ajouter pour l'interface spécifiée au lot 2.

Étendre le noyau et l'interface Qwen avec les actions constituées au lot 3.
Le modèle continue à fournir des propositions ; les incorporations consomment
les producteurs et les témoins de la tâche documentaire.

- Énumérer les effets disponibles et les relier à leurs transitions formelles.
- Rendre le contenu publiable depuis les éléments justifiés et leurs références.
- Écrire le livrable dans l'espace reçu, conserver le reçu de réalisation et
  vérifier par relecture les données effectivement écrites.
- Vérifier que les chemins, références, erreurs de décodage et reprises restent
  dans la portée du contrat et de la continuation prouvée.
- Réaliser la sauvegarde et le chargement de la mémoire retenue. Tester un arrêt
  du processus puis une reprise depuis le checkpoint, distincte d'un rejeu
  depuis l'initialisation.
- Raccorder le timeout et les erreurs du modèle à l'absence de proposition
  prévue au lot 4. Raccorder les erreurs d'effets aux réponses et conditions
  d'environnement déclarées.
- Maintenir l'accord entre le résultat partagé, l'état suivant, les messages
  publiés et les reçus ; inspecter les dépendances du code généré.
- Documenter le passage du modèle formel des effets à l'adaptateur exécuté, ainsi
  que la frontière de confiance du runtime, du compilateur et du système.

**Livrable :** agent local exécutable, dossier produit, références vérifiables,
reçus des effets, sauvegarde/reprise depuis le présent et procédure de rejeu.

**Critère de sortie :** un lancement depuis l'état réduit accomplit une tâche
admissible et réalise le dossier annoncé, avec les effets et les justificatifs
correspondant à la même exécution.

## 7. Éprouver, relire et préparer l'intégration

**But :** livrer un résultat mathématique et une expérience reproductible sur
une révision précise.

**Appui existant :** la gate complète, les contrôles du code généré, le transport
et le rejeu du premier raccordement passent. L'extension reçoit son protocole
et ses résultats propres ; elle conserve les expériences de référence.

Figer le nouveau protocole, les sources, les poids, les réglages, les graines,
les tâches, les moments d'oubli et les critères de réussite avant le run confirmatoire.
Conserver les smoke tests avec leur statut propre et garder les textes bruts
du modèle hors du dépôt.

| Situation à éprouver | Obligation examinée |
| --- | --- |
| Oublis avant et après des productions dépendantes | Accord des futurs et maintien de la possibilité d'accomplissement |
| Propositions erronées répétées et absence de proposition | Continuation de progrès et terminaison de la procédure |
| Lectures autorisées ou autres propositions valides répétées sans progrès | Accomplissement ou diminution stricte de la mesure dans la borne de tours annoncée |
| Effacements du contexte entre ces propositions sans progrès | Conservation des ressources de l'ordonnanceur et absence de réinitialisation de son compteur éventuel |
| Demande de modification du contrat par le modèle | Persistance du contrat reçu |
| Occurrences de même valeur, avec des origines ou permissions différentes | Conservation des identités pertinentes |
| Référence ancienne, absente ou devenue incohérente | Préservation des anciennes lectures ou refus fondé selon le contrat |
| Proposition de publication sans justification suffisante | Absence d'incorporation et continuation du travail utile |
| Accès ou écriture hors portée | Concordance entre permissions et effets disponibles |
| Tâche inadmissible | Diagnostic conforme, distinct de l'accomplissement |
| Arrêt du processus et chargement d'un checkpoint réduit | Accomplissement effectif depuis la mémoire chargée, avec accord des futurs |
| Extension du contrat après oubli | Nouvelle justification de la mémoire et diagnostic si une ressource requise manque |

Mesurer séparément conformité, obligations accomplies, reprises, propositions
refusées, informations retenues, octets, appels au modèle et coûts d'exécution.
Les observations mettent à l'épreuve la réalisation ; les théorèmes gardent
leurs quantifications et leurs hypothèses.

Exécuter les vérifications appropriées puis la gate complète du dépôt. Relire
le texte sans les noms Lean, puis confronter ses conclusions aux énoncés et
à leurs consommateurs. Préparer les matériaux d'une revue indépendante sur
un commit précis ; sa soumission suit une instruction explicite.

Préparer enfin l'interface destinée à la production, le classement des modules,
les passages canoniques et les entrées du registre. Les changements de dépendance
rouvrent les revues correspondantes. Les documents temporaires de `docs/work`
seront remplacés par les livrables permanents avant une intégration autorisée
dans `main`.

**Livrable :** protocole, résultats, certificat final, rapport lisible et lot
d'intégration concret.

**Critère de sortie :** conformité, mémoire exacte, progrès, terminaison et
réalisation du dossier sont établis dans leurs portées respectives et raccordés
sur la même instance exécutée. Les obligations encore ouvertes sont identifiées.

## Ordre de travail et validation finale

| Lot | Dépendances | Résultat qui autorise la suite |
| --- | --- | --- |
| 1 — Référence | Premier raccordement réalisé et revérifié | Révision et évidence cohérentes |
| 2 — Tâche et contrat | 1 ; essai de raccord du lot 3 | Spécification indépendante, effets reçus et instance admissible |
| 3 — Constitution et actions | Essai avec le lot 2, puis contrat fixé | Raccord sémantique, producteurs concrets et préservations fermées |
| 4 — Accomplissement | 3 | Progrès borné pour toute politique, continuation exécutée et terminaison démontrée |
| 5 — Présent et oubli | 3 ; fermeture conjointe avec 4 | Futurs exacts, accomplissement conservé et lois du checkpoint |
| 6 — Effets réels | Interface reçue au lot 2 ; lois des lots 3 à 5 | Dossier et checkpoint réalisés, accord de l'adaptateur fermé |
| 7 — Livraison | Obligations des lots 2 à 6 fermées | Résultat reproduit et lot relu sur sa révision |

Les lots 2 et 3 commencent par un essai commun : une action documentaire entière
valide la faisabilité du raccord. Le contrat et le critère d'accomplissement
sont ensuite fixés avant la procédure complète. Les effets peuvent être réalisés
après les preuves abstraites si l'adaptateur ferme exactement leurs lois. La
garantie finale exige aussi cet accord de réalisation.

### Acquis revérifiés du premier raccordement

- [x] Chaîne constitutive, regroupement et exécuteurs du présent identifiés avec leurs contrats.
- [x] Composition adaptative, conservation du contrat et des lectures, accomplissement de `obtain` permis.
- [x] Oubli des profils et domaines des preuves de minimalité distingués.
- [x] Expérience Qwen, quatre effacements de contexte, empreintes, transport, rejeu exact et gate complète vérifiés.
- [x] Révision de référence du raccordement fixée par le commit de livraison.
- [ ] Enregistrement de la nouvelle évidence scientifique sur cette révision.

### Obligations de l'extension documentaire

- [ ] Une action documentaire complète valide le raccord avant de figer l'application.
- [ ] Contrat reçu, ressources, admissibilité, effets et accomplissement définis indépendamment de la procédure.
- [ ] Lois sémantiques du raccord, identités, dépendances et permissions fermées sur la même instance.
- [ ] Regroupements éventuels justifiés par les relations produites, avec conservation des identités sources.
- [ ] Conformité pour toute politique dans le nouveau langage.
- [ ] Progrès dans une borne de tours construite depuis le présent, pour toute politique, y compris les propositions valides sans progrès.
- [ ] Composition de ces progrès bornés en une preuve de terminaison globale, avec conservation des ressources de l'ordonnanceur après oubli.
- [ ] Projection exacte pour tous les futurs documentaires, accomplissement conservé et distinction effectivement oubliée.
- [ ] Sauvegarde, chargement et reprise depuis la mémoire retenue, avec leurs lois d'accord.
- [ ] Livrable et effets réels raccordés aux mêmes productions et certificats.
- [ ] Nouvelle expérience Qwen figée, exécutée et rejouée, avec arrêt/reprise du processus.
- [ ] Contrôles Lean, audits, liens, registre, portée et préparation de l'intégration vérifiés.

La suite du **lot 1** consiste à enregistrer la nouvelle évidence scientifique
sur la révision de livraison.
La première construction nouvelle est l'essai commun des **lots 2 et 3** :
une source, une occurrence, une action avec préservation et un élément de dossier
réalisé. Cet essai doit établir le raccord qui permettra de fixer la classe
documentaire, puis de fermer son accomplissement et ses futurs après oubli.
