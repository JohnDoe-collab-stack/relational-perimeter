# Relecture du plan d’alignement à partir du code Lean

**Date :** 9 octobre 2026. **Branche :** `codex/ai-alignment-under-contract`.
**Base :** `b71904ab3b1cabb18faec791a690fa87b434e00e`.

Cette relecture confronte le [plan documentaire](plan-alignement-agent-dossier.fr.md)
et sa dernière critique aux énoncés, aux constructions et aux consommateurs du
code. Au moment de cette relecture, les fichiers du raccordement local
n’étaient pas encore commités.
Le protocole confirmatoire identifie cet arbre par 251 empreintes de sources et
de configurations. Leur accord avec les fichiers actuels a été vérifié.

## Verdict

Le projet possède déjà une chaîne exécutable et certifiée de constitution,
recherche, action, préservation, regroupement et continuation. Il possède aussi
des réalisations exactes des futurs, un oubli irréversible de profils sources
et une preuve de minimalité comportementale du noyau machine sous son contrat.
Le raccordement local compose l’exécuteur constitutif avec les propositions
d’un modèle réel. Les garanties de ce raccordement quantifient sur toute
politique adaptative dans son langage déclaré.

Le plan doit partir de ces résultats fermés. Son travail nouveau consiste à
instancier ou étendre leurs interfaces pour une tâche reçue plus riche, à fermer
les lois de cette instance et à raccorder ses effets réels. Présenter ces lots
comme la reconstruction de mécanismes encore hypothétiques sous-estimerait
le code existant.

Deux obligations proposées demandent effectivement du travail supplémentaire :
la constitution documentaire et son critère d’accomplissement ; une procédure
qui accomplit cette tâche globale même si le modèle ne propose jamais d’action
utile. Cette seconde obligation est plus forte que le résultat actuel de
production et de réponse pour toute demande `obtain` permise.

## 1. Les trois niveaux à distinguer

| Niveau | Construction et contrat propres |
| --- | --- |
| Maître constitutif | `UnifiedMaster.publicInstance` produit une exécution de ressources. Les rôles, la normalisation, le régime, les obligations et le point de reprise se rattachent à cette exécution. |
| Machine avec routage SAT | `MasterMachine.receive` reçoit le maître, un scope, une formule et des contextes SAT. Ses requêtes entrelacent opérations du noyau, routages et lectures du problème. |
| Agent relié à Qwen | `Agent.Memory` conserve le contrat de restitution, le moteur vivant et le registre de cibles. `ModelLoop` et `Kernel` incorporent les opérations `advance`, `inspect`, `obtain`, `propose`. |

Les deux applications consomment des constructions du même maître. Le runner
Qwen actuel n’appelle cependant pas le runtime SAT combiné. La minimalité du
noyau machine n’est pas, par ce seul partage, une minimalité du registre de
l’agent ni de l’état SAT combiné.

Références : [UnifiedPublicCertificate.lean](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean),
[MasterRuntime.lean](../../RelationalPerimeter/Computation/Machine/MasterRuntime.lean),
[State.lean](../../RelationalPerimeter/Agents/Constitutive/State.lean),
[ModelLoop.lean](../../Tests/LocalAlignment/ModelLoop.lean).

## 2. Chaîne constitutive effectivement vérifiée

### Formation, recherche et action

Le maître reçoit des primitives et un contexte déclaré. Dans
`MasterResources`, la recherche lit un port source antérieur ; son résultat
indexe une nouvelle ressource. L’application lit cette découverte et la
fraîcheur disponible. La décomposition lit l’application et le préfixe constitué.
`executeWithReferences` produit la tête, ses transports de références et le
successeur avant de poursuivre depuis ce successeur.

La recherche suivante consomme la génération, la graine et la provenance du
présent. `runThreadedNextDiscovery` exécute l’extraction, le filtrage et la
recherche enregistrée. `buildFromExecutedDiscovery` consomme ce résultat déjà
obtenu. Le constructeur ne reçoit pas un journal libre ou une solution à
certifier après coup.

L’action complète `applyFullConstitutiveStep` est définie sur une continuation
structurelle sans recevoir son acceptation comme argument. La préservation du
critère est démontrée séparément par
`applyFullConstitutiveStep_preservesAccept`. Le résultat de l’action alimente
l’état opérationnel suivant.

Références : [MasterResourceExecution.lean](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/MasterResourceExecution.lean),
[ConstitutiveFeedback.lean](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ConstitutiveFeedback.lean),
[CausalOperationalExecution.lean](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/CausalOperationalExecution.lean),
[ConstitutiveFullStep.lean](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ConstitutiveFullStep.lean).

### Regroupement et identités

`ExecutedOutput.policy` se construit à partir des images des sorties locales
produites. `ExecutedCausalNormalization.result` élimine la chaîne constitutive
stockée pour produire cible et trace. Son autorisation extrait de cette même
chaîne la préservation, la constitution relationnelle et la séparation des
occurrences.

Les obligations autorisées sont la réalisation de cette image, avec des lois
de retour. La convergence des cibles est un théorème de l’exécution ; la largeur
un est une conséquence aval. L’égalité des obligations est exactement l’égalité
des cibles produites, et équivaut à une codétermination munie des deux traces.
Le maître construit également deux profils distincts portés ensemble.

Le regroupement est donc déjà réalisé et prouvé dans cette instance. Pour un
dossier, l’obligation sera de constituer les nouvelles relations pertinentes et
de fermer leurs lois de préservation. Une égalité de texte ne fournit pas ces
lois.

Références : [ExecutedOutputObligations.lean](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ExecutedOutputObligations.lean),
[ExecutedCausalNormalization.lean](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ExecutedCausalNormalization.lean),
`UnifiedMaster.Instance.distinctPair` et `facts` dans le certificat du maître.

### Présent et continuation

`LiveContinuation.produce` exécute la recherche depuis la mémoire retenue,
construit l’action et sa décomposition, puis forme le prochain présent.
`production_exact` et `next_exact` ferment l’accord avec le moteur riche.
`execute` partage chaque production entre événement et successeur.

Dans le noyau machine, `ConstitutiveExecution.buildAction` utilise la découverte,
le schedule produit, sa validation et son exécution. `produce`, `perform` et
`run` sont des procédures concrètes. Leurs lois d’accord sont démontrées ; elles
ne sont pas des interfaces génériques laissées à réaliser.

Références : [LiveResourceContinuation.lean](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/LiveResourceContinuation.lean),
[ConstitutiveLiveExecution.lean](../../RelationalPerimeter/Computation/Machine/ConstitutiveLiveExecution.lean).

## 3. Futurs, oubli et minimalité : portée exacte

| Résultat fermé | Quantification et distinction conservée |
| --- | --- |
| Futurs de l’agent | `Persistence` conserve états projetés, événements, lectures et admissions dans les deux sens pour toute liste finie de requêtes de son langage. Les autorisations riches et réalisées ont leurs lois de retour. |
| Oubli des profils | Deux profils initiaux distincts produisent la même mémoire après normalisation. Aucun récupérateur uniforme ne retrouve tous ces profils depuis cette mémoire. Les exécutions futures correspondantes sont identiques. |
| Composition adaptative | À politique, contexte initial et entrées identiques, les profils normalisés donnent la même exécution adaptative. L’irrécupérabilité dans l’état composé fixe explicitement le contexte initial. |
| Minimalité du noyau | À scope fixé et sur les mémoires cohérentes, égalité de projection si et seulement si égalité de tous les futurs. Toute autre réalisation exacte doit conserver ces distinctions comportementales. |
| Futurs SAT combinés | Toute liste finie du langage combiné conserve lectures, admissions et événements, avec le routage réellement configuré. La frontière SAT est conservée ; sa minimalité n’est pas affirmée. |

Les théorèmes d’oubli portent sur les profils effectivement consommés par la
normalisation. Ils ne disent pas que toute information chronologique est devenue
irrécupérable. `MasterContinuationFeasibility` démontre même une reconstruction
des préfixes canoniques lorsque le contrat impose de retrouver profondeur et
provenance complètes. Ce résultat utilise ce contrat plus fort ; il n’en affirme
pas la nécessité pour toute interface suffisante.

La suppression de supports historiques, l’oubli irréversible d’un profil et
l’effacement du transcript du modèle sont donc trois opérations à examiner
avec leurs domaines respectifs. Le premier raccordement possède déjà les deux
dernières, dans les portées formelle et expérimentale annoncées.

Références : [Persistence.lean](../../RelationalPerimeter/Agents/Constitutive/Persistence.lean),
[Agreement.lean](../../RelationalPerimeter/Agents/Constitutive/Agreement.lean),
[ReducedLiveMinimality.lean](../../RelationalPerimeter/Computation/Machine/ReducedLiveMinimality.lean),
[MasterContract.lean](../../RelationalPerimeter/Computation/Machine/MasterContract.lean),
[MasterContinuationFeasibility.lean](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/MasterContinuationFeasibility.lean).

## 4. Conformité, production et accomplissement

L’autorisation actuelle consomme une référence de permission, une occurrence
du registre, son emplacement exact et l’égalité avec sa lecture. La cible
possède une origine dépendante : licence de normalisation exécutée ou production
de continuation. Son acceptation découle de cette origine.

`performCertified` construit des réponses et des refus fondés. Le critère
propositionnel `ReplyCriterion` est plus faible : ses branches de refus et
d’avance valent `True`. La justification précise des refus se trouve dans
`ResponseEvidence`, qui est effectivement construit et consommé. La lecture
doit garder ce témoin plus riche.

Pour une demande `obtain` permise, la procédure construit exactement
`handle + 1 - register.length` étapes et rend la réponse autorisée.
`obtain_produces_and_returns`, `obtain_work_exact` et
`permitted_obtain_answer` ferment ce résultat. Il existe déjà une tâche concrète
accomplie sous contrat après reprise depuis le présent.

Le raccordement adaptatif construit `CertifiedRun` pour toute politique, tout
état et toute suite finie de signaux. Il préserve le contrat et les anciennes
lectures. Cela ne contraint pas la politique à demander une action utile.

Dans l’expérience locale, l’effacement concerne les anciens messages envoyés
au modèle ; le processus du noyau conserve sa mémoire constituée. Le rejeu
repart de l’initialisation et réexécute les requêtes enregistrées. Une reprise
après arrêt du processus, depuis un checkpoint sauvegardé, demandera son
encodage, son chargement et leurs lois d’accord. Cette obligation appartient
aux nouvelles reprises et aux effets des lots 5 et 6.

Cette différence a été vérifiée par un client Lean provisoire hors du dépôt :
une politique constante proposant `none` conserve exactement l’état initial
sur toute suite finie de signaux, y compris les effacements. Les quatre
déclarations du client compilent sans axiome. Ce cas montre pourquoi une
terminaison globale indépendante de toute proposition utile demande une
procédure supplémentaire. Il ne retire rien à la production positive pour
les demandes permises.

Références : [ProducedEvidence.lean](../../RelationalPerimeter/Agents/Constitutive/ProducedEvidence.lean),
[Execution.lean](../../RelationalPerimeter/Agents/Constitutive/Execution.lean),
`obtain_produces_and_returns`, `obtain_work_exact`, `ReplyCriterion` dans Agreement,
et [ModelLoop.lean](../../Tests/LocalAlignment/ModelLoop.lean).

## 5. Corrections de ma dernière critique

1. **Continuation depuis la mémoire retenue.** Elle est déjà construite dans
   les instances concrètes. Mon renvoi à l’interface générique
   `SignatureDynamics` ne devait pas suggérer que cette réalisation manquait.
   L’obligation nouvelle concerne son extension à la tâche documentaire.
2. **Regroupement.** Il est déjà dérivé des productions, avec séparation des
   profils et préservation sémantique. Le plan doit citer cet acquis et définir
   les lois de sa nouvelle application.
3. **Contribution du modèle.** Elle existe déjà : ses requêtes déterminent les
   productions et lectures demandées, et ses valeurs candidates sont examinées.
   Une contribution documentaire plus riche doit être décrite ; rendre le modèle
   indispensable n’est pas une condition de la preuve de conformité.
4. **Ordre des effets et de la mémoire.** Le plan prévoit bien les effets dans
   le contrat au lot 2. Réaliser l’adaptateur après les preuves abstraites est
   possible si ses lois d’accord ferment exactement ce contrat. L’ordre des
   lots n’est donc pas en lui-même un défaut mathématique.
5. **Accomplissement.** La production-réponse permise est acquise. L’ordonnanceur
   qui termine un dossier malgré une politique toujours inutile est une
   exigence supplémentaire proposée par le plan.

## 6. Ce que chaque lot doit réellement ajouter

| Lot | Appui existant | Obligation nouvelle |
| --- | --- | --- |
| 1 — Référence | Preuves, protocole et expérience vérifiés | Révision de référence et enregistrement de l’évidence lorsque la livraison est demandée |
| 2 — Tâche | Contrat reçu et critères de réponse indépendants | Domaine documentaire, ressources, permissions, admissibilité et critère d’accomplissement propres |
| 3 — Constitution | Producteurs, chaînes exécutées, autorisations, préservations et regroupement | Raccord sémantique concret des informations et actions documentaires à ces constructions |
| 4 — Accomplissement | Continuation exécutable et accomplissement de `obtain` | Procédure et preuve de terminaison globale pour la classe documentaire choisie, si cette garantie forte est retenue |
| 5 — Mémoire | Accords de futurs, oubli des profils et minimalité du noyau sous son contrat | Réalisation exacte pour les nouveaux futurs documentaires et distinction réellement oubliée dans ce domaine |
| 6 — Effets | Transport brut certifié, sorties Lean, modèle réel et rejeu exact | Réalisation du dossier et accord des nouveaux effets avec leurs transitions formelles |
| 7 — Livraison | Gates, contrôles du code généré et expérience figée | Protocole de l’extension, révision précise, revue et intégration autorisée |

Le premier dossier doit être choisi en fonction d’un raccord concret à cette
chaîne. L’instance actuelle de l’agent lit des continuations SAT par variables
booléennes ; cela délimite cette interface, sans réduire toute la théorie à
ce readout. Les sources documentaires, leurs droits et leurs règles de
construction demandent leur propre réalisation.

Le périmètre exact est lui aussi déjà formalisé : correspondance dans les deux
sens entre exigences et occurrences, accord local, frontières séparées,
continuation positive au-delà du périmètre et classification du régime
circulaire. Ces résultats consomment les données de `CircularPresentation`,
dont ses témoins de compatibilité et d’obstruction. Les appliquer à un dossier
exige une instance qui ferme ces obligations. La fin d’un dossier et la
poursuite de la génération peuvent alors être examinées avec ces critères
explicites. Référence : [StrongPerimetralTurning.lean](../../StrongPerimetralTurning.lean).

## 7. Contrôles exécutés pendant cette relecture

| Contrôle | Résultat |
| --- | --- |
| `scripts/verify.ps1` avec le Python configuré | Succès : build de 248 jobs, 246 fichiers Lean, stratification de 200 modules de production |
| Audit exhaustif | 20 868 constantes, 245 modules, 364 exceptions générées classées, aucune exception écrite |
| Fixtures de refus attendu | 23 diagnostics et sites attendus, sans erreur supplémentaire |
| Contrôles scientifiques intégrés | Auto-tests, statique : 18 affirmations et 81 déclarations ; clients Lean : 68 références publiques et 13 de tests |
| `run.py test-transport` | 14 lignes, 6 formes JSON incorrectes et rejeu exact avec l’autre profil initial |
| `run.py replay` sur le dernier transcript confirmatoire | Égalité exacte des douze paquets, empreinte finale identique à la référence |
| Protocole et transcript | 251 empreintes conformes à l’arbre ; douze propositions reliées aux sorties enregistrées ; anciens messages absents aux quatre reprises prévues |
| Lecture du C généré du raccordement | Un appel à `executeProducedInput` dans la branche exécutée de `dispatchCertified` ; un appel au dispatch dans `process`, résultat partagé entre état, reçu et observation |
| Client Lean de politique silencieuse | Quatre déclarations sans axiome ; absence de génération pour toute suite finie de signaux |

Empreinte SHA-256 du nouveau journal de la gate :
`f7fb6b65aa3cff477fb4dd6b8677c4d6a0bd4cd8faf6ee010a0cce7d71b57a8a`.
Empreinte finale du rejeu :
`5f4618e1a6ffb776ac33eebdede4805cc17c2aceebc55998baa450bb340bb375`.

La relecture a porté sur les énoncés et les constructions cités. La gate couvre
mécaniquement l’ensemble des fichiers ; elle ne remplace pas une lecture de
chaque ligne des 246 modules. Aucun nouveau run d’inférence ni audit extérieur
n’a été effectué. Le rapport constitue une relecture locale du chantier ; les
statuts de revue enregistrés conservent leurs évidences propres.

**Décision issue de cette vérification :** organiser la suite autour des
certificats et contrats existants, puis fermer les lois de la nouvelle instance.
Le dossier documentaire reste une application proposée à valider par ce raccord.
L’extension doit rendre visible ce qu’elle réutilise, ce qu’elle instancie et
ce qu’elle démontre en plus.
