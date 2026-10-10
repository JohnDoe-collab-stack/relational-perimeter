# Composition finie du dossier dans la même exécution maître

Une liste de demandes documentaires peut maintenant être exécutée jusqu'à son
accomplissement, lorsque chaque demande possède une source permise dans sa paire
reçue. Cette garantie est constructive et porte sur le dossier effectivement
produit. Chaque étape consomme le successeur et la mémoire de la précédente ;
les anciens éléments, leurs références et leurs témoins de permission sont
conservés.

Ce document décrit un incrément de développement sur
`codex/ai-alignment-under-contract`. Les nouveaux modules sont des clients Lean
dans `Tests.LocalAlignment`. Ils consomment la réalisation du maître existant.
Le protocole Qwen historique et ses résultats restent attachés à leur exécution
de référence.

## Entrées et critère reçus

Les sources sont reçues avec leurs versions, leurs extraits et leurs références
d'occurrence. Le contrat fixe les positions dont la restitution est permise.
Une obligation contient une demande et deux références candidates.

La demande conserve le critère de la
[première couche documentaire](premiere-couche-documentaire.fr.md) : un fait
typé, sa valeur et, éventuellement, une origine exigée. Le critère
`Goal (demands tasks) items` demande que chaque fait reçu possède un témoin
dans le dossier. Il est défini indépendamment du programme et des permissions.

La nouvelle admissibilité fournit, pour chaque obligation, une référence de
source reçue, sa permission et la preuve que sa lecture répond au fait demandé.
Elle fournit une solution primitive disponible ; aucun élément produit,
dossier achevé, résultat SAT ou certificat de la future exécution n'est une
entrée de cette admissibilité. Le programme reçoit les obligations et cherche
leurs réponses ; il ne reçoit pas cette admissibilité comme instruction de
choix. Celle-ci sert à démontrer sa réussite sur la classe annoncée.

Les données `Passage` restent des annotations typées reçues. Le rapport au
texte source et la vérité de celui-ci sur le monde gardent les critères
déclarés dans le plan. Cet incrément ne crée aucune règle de déduction nouvelle.

## Composition et ressources réellement consommées

Le [module de composition](../../Tests/LocalAlignment/DocumentaryDossier.lean)
constitue un état avec un curseur maître et la mémoire documentaire conforme.

À chaque obligation, `step` appelle une fois le
[raccord binaire](raccord-documentaire-maitre.fr.md). La tête exécutée fournit
la variable et le successeur ; les lectures et permissions déterminent le
problème reçu. L'ouverture, le regroupement et le transport de la continuation
déterminent l'origine effectivement extraite.

Le même paquet sert à constituer l'état suivant et la trace. La récursion
consomme cet état suivant. Elle ne recrée pas un curseur depuis l'origine et
ne remplace pas le dossier par une réponse anticipée.

Une demande bloquée ne crée aucun élément documentaire. Son refus conserve la
mémoire documentaire ; le maître a néanmoins produit le successeur de cette
étape, qui permet d'exécuter l'obligation suivante. Le critère commun peut donc
reconnaître les parties accomplies tout en déclarant le dossier entier incomplet.

La trace conserve les paquets riches effectivement produits et leurs états
indexés. Cet incrément n'effectue pas une projection de cette trace ou du
curseur vers une mémoire réduite.

## Énoncés fermés

| Déclaration dans `Documentary.Dossier` | Conclusion |
| --- | --- |
| `Execution.goal`, `accomplishment` | Toute liste admissible possède un témoin d'accomplissement dans le dossier de cette exécution réelle. |
| `completion_verdict` | L'évaluateur indépendant reconnaît cet accomplissement. |
| `exact_step_count` | Pour toute liste reçue, la profondeur finale vaut la profondeur de départ plus le nombre d'obligations, y compris les obligations bloquées. |
| `exact_item_count` | Pour une liste admissible, chaque obligation ajoute un élément au dossier. |
| `Execution.previous`, `Execution.previous_position` | Chaque ancienne référence est transportée ; son déplacement correspond exactement au nombre d'incorporations réelles. |
| `Execution.previous_evidence` | Le témoin de conformité de chaque ancienne occurrence est celui de la mémoire de départ. |
| `Execution.old_goal` | Toute demande déjà accomplie reste accomplie après cette continuation. |
| `execute_append`, `execute_append_events` | Exécuter un préfixe puis reprendre depuis son état produit donne le même état final et les mêmes événements que l'exécution de la liste entière. |
| `forbidden_list_incompatible` | Si une demande de la liste impose une origine interdite, aucun dossier conforme ne peut accomplir cette liste. |
| `execute_after_context_erasure` | Une remise à zéro du contexte extérieur conserve cette exécution depuis le même état maître et documentaire. |

La récursion sur la liste reçue ferme la terminaison de cette procédure finie.
La borne compte ses étapes maître. Elle ne mesure pas le temps physique, la
taille du support, ni les itérations internes de normalisation SAT.

Le théorème d'incompatibilité quantifie sur tous les dossiers conformes. Il
consomme une occurrence de la demande dans la liste, son origine exigée et
l'absence de permission. Il ne dépend pas d'un échec observé de cette procédure.

## Cas réalisé et vérifications

Le [client concret](../../Tests/LocalAlignment/DocumentaryDossierCases.lean)
reçoit les trois sources déjà utilisées par le raccord binaire. La demande
initiale vise le fait 42 ; la seconde vise sa version révisée 43. Le programme
produit deux citations avec leurs versions et origines distinctes.

Le [dossier rendu](dossier-fixture-compose.fr.md) est copié depuis ces deux
éléments effectivement constitués. Le client vérifie aussi :

- une demande à origine interdite placée entre deux demandes réalisables ;
- un fait indisponible, suivi d'une demande réalisable ;
- deux demandes égales qui produisent deux occurrences documentaires ;
- la liste vide, la reprise depuis un préfixe produit et l'effacement du contexte ;
- le transport exact de l'ancienne référence et de son témoin de conformité.

Les 21 contrôles du
[smoke](../../scripts/run-documentary-dossier-smoke.py) sont accompagnés de
680 cas générés depuis des littéraux reçus indépendamment du producteur Lean :
les huit ensembles de permissions, et toutes les listes de longueur zéro à
trois formées des quatre demandes du client. Le calcul attendu distingue
l'événement de chaque étape et l'accomplissement du dossier final.

Le [contrôle du C généré](../../scripts/check-documentary-dossier-codegen.py)
vérifie une seule consommation du raccord, une projection de l'état suivant
et un appel de la continuation par dépliage de la récursion. Les frontières
d'analyse sont nommées : la projection suivante et la queue récursive. Le
raccord binaire conserve ses propres contrôles. Trois altérations en mémoire
qui doublent un appel accessible sont rejetées par ce même contrôle.

Ces cas sont des essais construits de développement. Le smoke n'appelle pas
Qwen. La [fiche de vérification](composition-dossier-maitre-verification.json)
consigne les commandes, résultats et empreintes de cet incrément. Les résultats
des incréments antérieurs gardent leurs empreintes historiques.

La gate complète a réussi sur 253 fichiers Lean : 21 667 constantes dans 252
modules, aucune exception pour les déclarations écrites. Les 84 audits choisis
dans les deux nouveaux modules sont sans axiome. Les 23 fixtures de refus attendu
du dépôt passent ; deux clients temporaires supplémentaires sont rejetés au
typage lorsqu'ils remplacent le successeur réel par l'état d'origine ou effacent
le dossier produit avant de poursuivre.

## Suite du plan

La composition des demandes d'extraction est fermée sur cette classe. Les
[lots 2 et 3](plan-alignement-agent-dossier.fr.md) doivent encore porter les
dépendances entre éléments et les règles de déduction annoncées. Des sections
distinctes imposant une structure propre de livrable demanderont leur critère
supplémentaire ; le critère actuel porte sur la liste des faits reçus.

La procédure finie n'est pas encore entrelacée avec les propositions adaptatives
du modèle. Le lot 4 doit fermer son progrès borné dans cette interaction, y
compris avec des propositions valides sans progrès. Les futurs exacts de la
mémoire documentaire réduite, la sauvegarde et le chargement, les effets sur
fichiers et les comparaisons avec/sans restent les obligations suivantes du plan.
