# Accomplir le dossier malgré les propositions et les effacements du contexte

La continuation documentaire possède maintenant une garantie de progrès qui
quantifie sur **toute politique de proposition**. Pour une tâche admissible
de la classe finie déjà constituée, l'exécution atteint le dossier accompli
en autant de tours contrôlés qu'il reste d'obligations. Une politique peut
se tromper, ne rien proposer ou répéter des lectures sans progrès : cette
garantie reste valable. Le critère reçu et les permissions sont conservés.

Ce résultat est établi dans [DocumentaryAdaptive.lean](../../Tests/LocalAlignment/DocumentaryAdaptive.lean).
Les [cas fermés](../../Tests/LocalAlignment/DocumentaryAdaptiveCases.lean)
consomment leurs traces effectives pour construire les certificats.
La revendication candidate `DOCUMENTARY_ADAPTIVE_BOUNDED_COMPLETION` et les
contrôles de développement sont consignés dans le
[relevé de vérification](continuation-documentaire-adaptative-verification.json).
L'incrément prolonge les [programmes mixtes](programmes-documentaires-mixtes.fr.md).

## Ce qui porte le progrès

Le présent retient les occurrences et leurs justifications, les liaisons vers
les sorties déclarées, le curseur du maître, les obligations restantes et le
compteur de tours. Le contexte de proposition est une composante distincte.
L'observation donnée à la politique contient le critère courant, le nombre
d'occurrences disponibles et de sorties déclarées, la profondeur du maître,
le tour et le résumé réel du tour précédent. Elle ne reçoit pas le dossier
achevé comme entrée.

La politique rend au plus une proposition par tour. Les propositions portent
sur l'instruction courante, l'ordre de ses sources, une inspection, une paire
de sources ou une déduction utilisant une occurrence de règle et deux sorties
antérieures. Les positions numériques sont résolues en références typées.
La transition consomme ensuite les producteurs et permissions existants.

| Proposition | Transition effective |
| --- | --- |
| Instruction reçue exactement | Exécution de cette instruction une fois |
| Paire de sources renversée | Recherche du même fait avec la paire renversée, une fois |
| Autre paire ou déduction décodable | Tentative proposée, puis instruction reçue depuis l'état réellement produit |
| Inspection d'une sortie disponible | Lecture de son occurrence, puis instruction reçue |
| Absence ou proposition invalide | Instruction reçue |

Une proposition reconnue n'est pas automatiquement une action permise. La
tentative peut être refusée ou manquer de prémisses. Une déduction permise peut
également manquer l'objectif. Son occurrence reste alors dans le support avec
sa formation ; elle ne remplace pas la sortie requise. La continuation utilise
les ressources et liaisons transportées pour produire cette sortie. Les
permissions des sources et des règles restent celles du problème reçu.

Chaque obligation possède une réalisation construite depuis les ressources
du présent sous les conditions d'admissibilité déjà définies. Une source
permise de la paire doit satisfaire la demande ; une règle permise doit
transformer toutes les prémisses conformes en une conclusion conforme.
Ces témoins d'entrée ne fournissent ni exécution achevée ni valeur calculée.

`one_turn_accomplishes` établit la réalisation de l'obligation courante après
la transition réelle, pour toute proposition. La longueur de la file diminue
strictement. `Execution.complete` compose ces progrès depuis la trace conservée.
`all_policies_accomplish` porte sur tout état initial complet, tout programme
admissible de cette classe, toute politique et toute suite de signaux.

Pour n obligations restantes, `Execution.rounds` établit exactement n tours
supplémentaires. `Execution.bound` établit au plus 2n tentatives d'étape
documentaire. La fonction `Execution.attempts` compte les événements d'étape,
y compris les refus et les dépendances manquantes ; elle ne compte pas seulement
les occurrences incorporées. Les inspections et l'inférence ont leurs opérations
propres. La borne annonce des transitions contrôlées, sans borne de temps
physique ou de coût total.

## Le choix proposé a un effet réel

Une fixture distincte reçoit deux versions permises de la même mesure 42.
Le maître choisit l'occurrence 2 avec la paire reçue ; le renversement proposé
lui fait choisir l'occurrence 1. Les deux dossiers satisfont la demande, mais
ils citent des versions et des occurrences différentes. Le choix modifie la
recherche effectivement reçue et la production constituée. Le même paquet
réel fournit l'état suivant, la citation et son incorporation.

L'ordre des obligations et leurs dépendances restent reçus. Cette procédure
ne découvre pas de règle supplémentaire et ne réordonne pas un graphe général.
Sa quantification générale concerne le langage des extractions binaires et
des sommes et différences sur les annotations entières reçues.

## Une erreur permise reste visible

Le cas hostile reçoit les cinq tâches : mesure 42, révision 43, différence 1,
nouvelle citation 42, puis somme 2 de la différence avec elle-même. Il propose
trois extractions depuis la source interdite 0, une règle interdite et une
différence de la même prémisse avec elle-même, égale à 0.

Les quatre tentatives interdites sont refusées. La différence 0 est permise,
incorporée et conservée. Elle manque le dernier objectif ; la somme requise 2
est ensuite réellement produite. Les cinq sorties requises sont accomplies
en cinq tours, avec dix tentatives et six occurrences incorporées. Les six
têtes du maître correspondent aux tentatives d'extraction réelles.

La conclusion terminale conserve les origines `[1, 2, 1, 2]`, les versions
`[1, 2, 1, 2]` et les règles `[1, 0, 0]`. Son témoin vient de la trace conservée.
Le [dossier rendu](dossier-fixture-adaptatif.fr.md) lit les citations et cette
conclusion dans le support effectivement constitué.

Les deux citations de valeur 42 restent des occurrences distinctes, aux
positions 5 et 2 du support final. Les liaisons antérieures sont transportées
vers ces occurrences effectivement formées. L'égalité des valeurs ne fusionne
ni les identités ni les dépendances.

Un autre cas propose la différence dans l'ordre inverse : la conclusion −1
reste disponible, puis la différence 1 requise est produite. Le dossier se
termine correctement. Une tâche qui exige une règle interdite reste au
contraire incompatible : le refus ne devient pas un certificat de réussite.

## Effacement et continuation

Le contexte peut être réinitialisé avant chaque choix. Le cadre, les liaisons,
le compteur et la file restent dans le présent. Après trois tours, la reprise
reçoit les deux obligations restantes et le compteur 3. L'exécution termine
au tour 5. `Execution.bindings` conserve les références vers les occurrences
antérieures par le transport réel, avec leurs lectures et leur injectivité.

`all_policies_after_reset` conserve la garantie d'accomplissement après
l'effacement. Une autre proposition peut être choisie après cet effacement et
produire des occurrences supplémentaires différentes. L'égalité de tous les
futurs riches et réduits et la minimalité d'une mémoire documentaire demandent
encore les lois du lot 5. La reprise prouvée ici est une continuation depuis
l'état en mémoire ; la persistance après arrêt du processus reste un autre lot.

## Conditions d'exécution et contrôles

La politique formelle est une fonction totale. Chaque tour reçoit une
proposition ou une absence et accède aux ressources conservées. Aucun choix
favorable ou hypothèse d'équité du modèle n'est exigé. Pour le raccord futur
à l'inférence locale, un dépassement du délai devra produire l'absence prévue
par cette interface ; cette condition reste à réaliser dans l'adaptateur.

Les contrôles exécutables couvrent 31 vérifications fixes et 2 048 cas
comparés à un oracle indépendant de littéraux. Ils font varier faits,
permissions des trois occurrences de règles, source imposée interdite ou
publique, objectif correct ou décalé, huit politiques et effacement avant
chaque tour ou contexte conservé. L'oracle distingue les ports de tâche de
l'inventaire chronologique et compare valeurs, positions, inventaire complet,
événements, routes, lectures, têtes du maître, compteur et verdict final.
Sept audits du client sont contrôlés. Le rendu est comparé octet par octet
à une fixture indépendante.

Le contrôle du C compte sept chaînes d'applications et quatre sites directs :
tour courant, récursion suivante, signal reçu et choix proposé. Neuf mutations
de duplication ou de rejeu sont rejetées ; deux captures statiques non prises
en charge sont également rejetées. L'analyse traite exactement une capture
booléenne numérique et conserve la cible de sa fermeture. La politique,
l'environnement et le moteur générique du certificat sont des frontières
explicites. Ce contrôle de partage complète les preuves Lean.

La gate complète passe sur 259 fichiers Lean et 22 779 constantes de 258
modules. Les 93 déclarations sélectionnées des deux nouveaux fichiers sont
sans axiome. L'audit exhaustif ne trouve aucune exception dans les déclarations
écrites ; les 364 exceptions générées par le compilateur restent classées
séparément. Les 23 fixtures historiques de refus attendu passent aux sites
exacts. Les 11 sources mathématiques documentaires antérieures et les cinq
relevés précédents restent inchangés. Les commandes et empreintes figurent
dans le relevé.
Les expériences historiques et leurs empreintes restent conservées. Ce lot
utilise des politiques construites, sans nouvelle inférence du modèle et
sans comparaison avec/sans. La prochaine étape formelle est le contrat de
futurs documentaires du [plan](plan-alignement-agent-dossier.fr.md).
