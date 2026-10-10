# Accomplissement de programmes documentaires mixtes

Le nouvel incrément reçoit une tâche entière : des extractions et des déductions
entrelacées, avec des références typées vers leurs productions antérieures.
Lean construit l'accomplissement de **l'exécution réelle de tout programme
admissible de ce langage fini**. L'admissibilité apporte les permissions et
les lois de compatibilité des règles avec les critères reçus ; elle n'apporte
ni dossier achevé, ni valeurs calculées, ni trace d'exécution.

La revendication candidate `DOCUMENTARY_FINITE_PROGRAM_COMPLETION` concerne
l'arbre de développement non commité. Le [relevé](programmes-documentaires-verification.json)
identifie les sources, commandes, contrôles et statuts de revue. Le travail
prolonge les [déductions](deductions-documentaires.fr.md) et le
[raccord au maître](raccord-documentaire-maitre.fr.md).

## Tâche reçue et critère indépendant

Une extraction reçoit un fait demandé, une origine éventuellement imposée et
deux références de sources. Une déduction reçoit l'occurrence d'une règle,
deux références vers des sorties antérieures et son propre critère : valeur,
occurrence de règle et origines. Les règles restent la somme et la différence
signée sur les entiers issus des annotations des passages reçus.

Le programme est fini et son ordre est reçu. Ses ports désignent les
spécifications déjà déclarées : une instruction ne peut désigner sa propre
sortie ni une sortie future. Cette grammaire reçoit un graphe de dépendances
déjà ordonné ; elle ne découvre pas l'ordre d'un graphe arbitraire.

Le critère `Complete`, défini avant l'exécuteur, exige que **chaque sortie
déclarée** soit liée à une occurrence réelle satisfaisant sa spécification.
Le décideur lit ces liaisons et leurs ressources. Il ne cherche pas ailleurs
une valeur égale pour remplacer une production absente ou incorrecte.

Les contrats précédents restent fixes : publication des sources reçues 1 et 2
permise, source 0 interdite ; catalogue différence, somme, différence, avec
les occurrences 0 et 1 permises et 2 interdite. Les passages et versions
restent ceux des cas précédents. Les nouvelles demandes concrètes imposent
positivement les origines publiques 1 et 2.

## Chaîne effective et preuve générale

Chaque extraction appelle la recherche documentaire du même maître. Son paquet
effectif fournit le curseur suivant, la mémoire du dossier et la sortie
autorisée déposée dans le support de connaissances. Chaque déduction résout
ses deux liaisons et transmet leurs références effectives au producteur
existant. L'incorporation conserve le support de l'action réellement produite.

Le support, les liaisons et la trace passent à l'instruction suivante.
Les anciennes références sont transportées avec préservation des lectures
et injectivité. Deux occurrences égales en valeur restent distinctes.
Le témoin d'accomplissement consomme la trace conservée et les certificats
de progrès de ses étapes ; il ne relance pas les productions.

Pour un état initial complet et tout programme admissible, `accomplish`
établit l'existence d'un témoin `Complete` dans l'état retourné par `execute`.
Le constructeur exécutable `Execution.complete` donne ce témoin depuis la
trace réelle. Pour une extraction, l'admissibilité fournit une référence
dans la paire reçue, sa permission et sa conformité au fait demandé. Pour
une déduction, elle fournit une permission et une loi : toutes les prémisses
satisfaisant les spécifications reçues donnent, par cette règle, une conclusion
satisfaisant la spécification reçue. Cette condition est suffisante ; elle
n'est pas présentée comme une caractérisation de toutes les tâches réalisables.

| Garantie | Déclaration principale | Portée |
| --- | --- | --- |
| Accomplissement réel | `accomplish`, `Execution.complete` | Tout programme admissible depuis un état initial complet |
| Préservation des ressources | `Execution.extension` | Toute exécution, même avec refus ou erreur d'objectif |
| Conservation des liaisons | `Execution.bindings` | Références vers les mêmes occurrences transportées |
| Événements et têtes du maître | `Execution.length`, `Execution.depth` | Un événement par instruction ; une tête par extraction, même refusée |
| Reprise depuis le préfixe produit | `execute_append` | Même état final que le programme composé |
| Verdict positif certifié | `succeeded_correct` | Le booléen positif fournit le témoin du critère complet |
| Règle interdite imposée | `forbidden_rule_incompatible` | Aucun état conforme ne satisfait le critère complet correspondant |
| Effacement du contexte auxiliaire | `execute_after_context_erasure` | Même exécution, état constitutif et contrats conservés |

Les [énoncés complets](../../Tests/LocalAlignment/DocumentaryProgram.lean)
et l'[instance fermée](../../Tests/LocalAlignment/DocumentaryProgramCases.lean)
entrent dans l'audit exhaustif. Les calculs internes ne sont pas comptés
comme de nouvelles recherches SAT.

## Accomplissement, erreur et poursuite

L'instance positive exécute : citation 42, citation révisée 43, différence 1,
nouvelle citation 42, puis somme de la même différence avec elle-même, égale à 2.
Les cinq sorties satisfont leurs critères. Trois recherches du maître et deux
déductions produisent cinq occurrences. Le [dossier rendu](dossier-fixture-programme.fr.md)
lit les trois citations et la conclusion terminale dans l'état effectivement
produit. Le certificat de la somme conserve les origines `[1, 2, 1, 2]`, les
versions `[1, 2, 1, 2]` et les règles `[1, 0, 0]`.

- Une différence autorisée vaut 1 alors que la demande exige 99. L'occurrence
  réelle reste liée à la sortie déclarée. La somme suivante la consomme et
  vaut 2. Le programme entier reste incomplet, puisque l'objectif 99 échoue.
- L'occurrence de règle 2 est interdite. Aucune conclusion n'est incorporée.
  Sa dépendance suivante est marquée manquante, sans prémisse de remplacement.
  Une extraction indépendante suivante réussit.
- La demande impose la source interdite 0. L'extraction est refusée, sa
  dépendance manque et une demande publique indépendante peut ensuite réussir.

Le refus ne valide pas la tâche et ne bloque pas artificiellement le reste
du programme. Une sortie incorrecte n'est pas supprimée pour masquer l'échec.
Les deux citations égales à 42 occupent les positions constituées distinctes
4 et 1 dans le support final.

## Vérifications et suite

La gate complète passe sur 257 fichiers Lean et 22 422 constantes de
256 modules. Les 105 déclarations sélectionnées des nouveaux fichiers sont
sans axiome ; l'audit exhaustif ne constate aucune exception dans les déclarations
écrites. Les 364 exceptions générées par le compilateur restent classées
séparément. Les 23 fixtures historiques de refus attendu passent sans erreur
supplémentaire. Les sources et relevés des incréments précédents restent inchangés.

Les contrôles de développement exécutent 26 vérifications fixes et 1 536
programmes comparés à un oracle Python de littéraux : deux faits parmi quatre
valeurs, huit ensembles de permissions, trois occurrences de règles, demande
de source interdite ou publique, objectif correct ou décalé de 1. L'oracle
compare valeurs, refus, dépendances manquantes, événements, occurrences,
curseur et accomplissement global. Cinq audits du client sont sans axiome.
Le rendu réel est comparé octet par octet à une fixture indépendante.

Le contrôle du C effectue sept comptes d'applications et deux contrôles de
sites directs du répartiteur. Six mutations dans une copie en mémoire du C
sont rejetées : duplication de l'étape, du dépôt, de l'incorporation, des deux
producteurs du répartiteur, et réexécution dans le certificat. La récurrence
suivante et le moteur générique du certificat sont des frontières annoncées.
Les fermetures abstraites de liaisons reçues sont hors du compte des sites
directs. Les formes numériques des champs scalaires générés sont reconnues
sans traiter une expression symbolique comme un scalaire. Ces contrôles
ciblent le partage, sans borne de coût total ou de mémoire physique.

Deux clients négatifs temporaires sont rejetés par le typage : référence à
une conclusion dans un contexte vide, et référence à une spécification absente
des sorties reçues. Les fixtures historiques restent séparées. Le relevé
consigne aussi les corrections de développement et la gate complète.

Cette étape fournit une classe de tâches mixtes avec accomplissement général
et réalisation concrète. Elle n'ajoute pas d'inférence Qwen ni de comparaison
avec/sans. Le prochain lot du [plan](plan-alignement-agent-dossier.fr.md) est
l'ordonnanceur documentaire adaptatif : traiter les propositions utiles,
incorrectes ou absentes du modèle et garantir le progrès jusqu'au dossier
achevé. L'équivalence des futurs après réduction de la mémoire documentaire,
le checkpoint durable et les effets sur les fichiers restent à fermer.
