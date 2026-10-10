# Présent documentaire, oubli et continuation sous contrat

Le présent documentaire peut perdre ses anciennes interactions tout en gardant
exactement les futurs déclarés et la capacité d'achever une tâche admissible.
Ce passage est maintenant construit en Lean pour la classe documentaire finie
des lots précédents. Il conserve les permissions, les occurrences réellement
produites, leurs formations et leurs justifications. Il ne demande aucune
réponse favorable de la politique de proposition.

Cette étape ferme les lois documentaires d'oubli et de continuation du lot 5.
Les lois du checkpoint sont établies sur un payload typé. Son encodage portable,
son écriture, son chargement depuis un fichier et sa reprise dans un nouveau
processus restent à réaliser avec le lot 6. Le lot 5 demeure ouvert sur cette
obligation de reprise durable ; un payload en mémoire ne la remplace pas.

Le [relevé de vérification](memoire-documentaire-verification.json) identifie
les sources, les commandes et les limites de cette étape de développement.
Les expériences historiques et leurs empreintes restent conservées. Aucun
nouvel appel au modèle local ni essai comparatif avec/sans n'est réalisé ici.

## Configuration reçue et langage des futurs

La configuration fixe le support des sources, les permissions, le catalogue
des règles avec leurs opérations et le programme typé restant. Les extractions,
différences et sommes gardent les critères et dépendances des lots antérieurs.
Les lois quantifient sur tout état retenu de ces types, toute politique totale,
tout signal reçu et toute suite finie du langage suivant.

| Requête | Action et observation |
| --- | --- |
| Progresser | Traiter au plus une proposition puis l'obligation courante ; conserver le résumé des actions effectives et avancer le compteur |
| Inspecter une position de tâche | Lire la référence liée à cette position, sa valeur et ses origines ; signaler une liaison absente |
| Observer le présent | Lire compteur, profondeur du maître, ressources disponibles, positions constituées, obligations restantes et verdict d'accomplissement |
| Réinitialiser le contexte | Appliquer le reset reçu au contexte courant ; conserver les ressources, le dernier résumé, les liaisons, la file et le compteur |

Une permission de contrôle pour demander un tour n'est pas une permission
d'incorporer n'importe quelle production. Les autorisations de source et de
règle continuent de décider les incorporations. Une inspection admise porte
une référence et une occurrence effectivement liée ; les admissions sont
transportées dans les deux sens, avec leurs témoins, après tout futur fini.

## Ce qui est conservé et ce qui est oublié

Le module [DocumentarySnapshot](../../Tests/LocalAlignment/DocumentarySnapshot.lean)
matérialise chaque fonction de liaison en une table finie de références.
Chaque lecture de position est conservée exactement. La restauration garde
les mêmes stores et dossiers ; la complétude est transportée dans les deux
sens. La table évite de conserver les anciennes fermetures de liaison qui
capturaient leurs frames précédentes. Aucune économie d'octets n'en est déduite.

Le présent retient le contexte courant de la politique, le dernier résumé,
le compteur, les ressources réelles, les origines, les justifications, les
liaisons et les obligations restantes. Le curseur du maître, ses supports et
la formation des ressources restent conservés. Ce lot ne les reconstruit pas
en présentant leurs valeurs comme de nouvelles ressources reçues.

La mémoire riche ajoute l'archive des interactions : signal reçu, proposition
effective, résumé du tour et compteur antérieur. Chaque entrée provient du
tour qui vient réellement d'être exécuté. La projection retire cette archive.
L'exécuteur réduit ne reçoit aucun accès à ses anciennes entrées. Le contexte
courant est un paramètre reçu et reste conservé : l'accord général n'affirme
pas qu'il ne contient aucun souvenir. La perte de la proposition est fermée
sur les deux préfixes concrets étudiés ci-dessous.

Le module [DocumentaryMemory](../../Tests/LocalAlignment/DocumentaryMemory.lean)
construit un seul tour effectif et partage son résultat entre le prochain état,
son événement, son extension de ressources et ses certificats. La mémoire
riche utilise ce même passage puis archive l'interaction. L'égalité des futurs
provient de cette construction et du contrat explicite qui ne relit pas l'archive.

## Accord exact et accomplissement

Pour toute suite finie de requêtes, les états projetés, événements, lectures,
admissions et verdicts d'accomplissement concordent. Les théorèmes
`all_futures_projection`, `all_futures_events`, `all_futures_reads`,
`all_futures_admission` et `all_futures_accomplishment` ferment ces passages.
La trace conserve aussi une extension réelle des supports et transporte les
références antérieures, leurs lectures et leurs liaisons.

La possibilité d'accomplissement survit à chaque requête et à leur composition.
Après un futur fini, une exécution de la file restante achève toute tâche
admissible depuis un frame complet. Pour n obligations restantes, elle ajoute
exactement n tours et au plus 2n tentatives d'étape. Les certificats consomment
la trace stockée. Ils n'exécutent pas une seconde fois les producteurs.

Une inspection ou un reset ne consomme pas une obligation. On ne déduit donc
pas la terminaison d'un environnement qui demanderait éternellement des
inspections. Chaque tour de progrès sur une file non vide diminue strictement
sa longueur ; terminer cette file garde la borne du lot 4.

Réinitialiser le contexte peut changer les propositions suivantes. Le cas
construit lit le contexte courant pour choisir entre une proposition et une
absence : le reset change effectivement ce choix. La garantie après reset
est la conservation des ressources et de l'accomplissement possible. L'accord
exact compare les exécutions riche et réduite recevant le même futur, resets
compris, et non deux politiques dont les entrées seraient différentes.

## Une distinction réellement perdue

Les [cas fermés](../../Tests/LocalAlignment/DocumentaryMemoryCases.lean)
exécutent deux préfixes depuis le même boot documentaire. L'un reçoit la
proposition d'extraire les positions 98 et 98 ; l'autre reçoit 99 et 99.
Ces positions sont absentes. Les deux tours réalisent la même obligation
courante, avec le même contexte suivant, les mêmes ressources, le même compteur
et le même résumé. Leurs archives conservent pourtant les propositions différentes.

Leur présent projeté est égal. Aucune fonction de ce présent ne peut retrouver
correctement les deux propositions. Cette impossibilité demeure après toute
continuation commune du langage déclaré. `cannot_recover` et
`cannot_recover_after_any_future` prouvent ce fait sur ces productions effectives,
sans introduire un indicateur artificiel destiné à être effacé.

| Accès pertinent | Statut dans ce contrat |
| --- | --- |
| Sources, catalogue, permissions et formations des occurrences | Conservés ; ils ne contiennent pas la distinction 98/99 de ces deux préfixes |
| Contexte courant, dernier résumé, compteur et file | Conservés et égaux dans le cas d'oubli |
| Archives de propositions et de signaux, journaux du modèle, anciennes traces d'exécution ou d'outils | Absents de l'interface réduite ; aucune opération du langage ne les relit |
| Nouvelle politique ou nouveau signal transportant une ancienne archive | Apport extérieur : ce ne serait plus le même futur reçu dans les deux exécutions |
| Lecture directe de l'archive riche | Distingue les préfixes ; l'ajouter au langage invaliderait cette projection pour le contrat élargi |

La perte démontrée concerne cette ancienne proposition. Elle ne démontre pas
l'irrécupérabilité de toute histoire de formation, ni celle des préfixes
canoniques du maître. Étendre le contrat oblige à réexaminer la mémoire requise.

## Distinctions que les futurs obligent à conserver

Deux extractions effectivement produites depuis deux versions permises portent
la même valeur 42, mais les origines 1 et 2. Une inspection les distingue.
Le contexte courant influence les prochaines propositions ; l'observation
distingue le compteur 3 du compteur 5 et annonce les obligations restantes.
Les tables conservent les positions distinctes des occurrences de même valeur.

Une tâche imposant l'occurrence de règle interdite reste incompatible après
projection. Ses dépendances manquantes restent manquantes ; une extraction
indépendante peut ensuite être réalisée. L'oubli ne transforme donc pas un
contrat incompatible en une tâche accomplissable. Les cas de reprise vérifient
les refus et les continuations permises séparément.

Ces séparateurs établissent la nécessité des distinctions annoncées dans les
futurs correspondants. Ils ne prouvent pas la minimalité de tout le payload.
La minimalité du noyau machine conserve son domaine propre et ne se transfère
pas automatiquement à cette mémoire documentaire.

## Checkpoint et frontière de réalisation

`save` construit un checkpoint versionné de l'état retenu ; `load` restitue
son payload sous la même configuration typée et rejette une version inconnue.
La loi de retour, l'accord de tous les futurs depuis l'état chargé et le
transport de son accomplissabilité sont prouvés. Le payload comprend les
ressources actuelles et la file restante ; son type indexe les sources,
permissions et règles reçues.

Le cas fermé sauvegarde après trois tours, charge le présent avec le compteur 3,
retrouve la déduction 1 d'origines [1, 2], puis termine les deux obligations
restantes au tour 5. La conclusion 2 conserve les origines [1, 2, 1, 2]. Cette
continuation consomme l'état chargé et sa trace, sans rejeu du programme depuis
le boot.

Ce checkpoint est une valeur Lean contenant des ressources typées et des
opérations sous configuration fixée. Ce n'est pas encore un format portable
de fichier. Le prochain adaptateur devra rendre ces ressources accessibles
dans un nouveau processus, vérifier son décodage, réaliser les effets de
sauvegarde et de chargement et fermer leur accord avec les lois présentes.
Ces obligations restent explicitement ouvertes dans le
[plan](plan-alignement-agent-dossier.fr.md).

## Vérification de développement

Les commandes reproductibles sont :

```text
lake build Tests.LocalAlignment.DocumentaryMemoryCases
python -B scripts/check-documentary-memory-codegen.py
python -B scripts/run-documentary-memory-smoke.py
pwsh -NoProfile -File scripts/verify.ps1
```

Le smoke compare 19 contrôles fixes et 648 cas à des attentes littérales.
Il croise huit politiques, deux régimes de contexte, six moments de reset et
six points de checkpoint ; 72 cas supplémentaires reprennent la tâche dont
une règle imposée est interdite. Il compare événements riches/réduits,
lectures, positions, inventaire, routes, admissions, compteur, profondeur,
obligations restantes et accomplissement. Les neuf audits du client sont contrôlés.

Le contrôle du C examine huit sites directs et l'absence de rejeu dans le
certificat fermé. Huit duplications et un rejeu injectés sont rejetés. Ce sont
des contrôles de sites compilés avec des frontières explicites, sans borne de
coût physique. La gate adaptative antérieure reste exécutée pour le partage
interne de chaque tour.

Les vérifications intermédiaires ont détecté une dépendance non constructive
introduite par une élimination de cas automatique ; l'énumération explicite
des constructeurs l'a supprimée. Des réductions complètes trop coûteuses ont
été remplacées par la consommation des témoins réellement stockés. Les lois
et la portée ont été relues après ces corrections ; aucun audit indépendant
n'est enregistré pour cet incrément.

La gate complète a réussi sur 262 fichiers Lean : 23 205 constantes dans 261
modules, aucune exception dans les déclarations écrites, 364 exceptions de
constructeurs générées classées séparément, et les 23 fixtures historiques de
refus attendus. Les 130 déclarations sélectionnées de cet incrément sont sans
axiome. Les 13 sources mathématiques documentaires antérieures, les six relevés
historiques et les 19 entrées du registre restent inchangés depuis l'incrément
précédent. Les quatre paragraphes cibles et les 18 premières entrées restent
ceux de la révision de base.
