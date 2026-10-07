# Un maître, une exécution intégrée

## Ce qui est construit

La machine reçoit le maître existant, une formule SAT, une frontière de
contextes constitués et des permissions de lecture. Elle ne reçoit ni une
partition des branches ni une largeur attendue.

Une reprise produit une seule action vivante. Le sélecteur découvert par cette
production sert à ouvrir les contextes SAT reçus. La recherche de relations sur
ces contextes construit simultanément la frontière retenue et son programme
de routage. La prochaine mémoire conserve cette frontière : la recherche
suivante lit donc ce que la précédente a effectivement retenu.

Dans cette famille vivante, la valeur du sélecteur est déterminée par la
profondeur (`LocalAction.selected_exact`). Cela n'est pas une nouveauté
informationnelle. Le chemin exécuté lit néanmoins le sélecteur retourné par
la recherche ; il ne le remplace pas par un calcul indépendant depuis la
profondeur. Le raccord est orienté : le moteur vivant fournit le sélecteur à
SAT, tandis que la frontière SAT produite alimente la recherche SAT suivante.
Il n'y a pas ici de retour de SAT vers le moteur vivant.

Le programme configure des gates finies. Les paquets ultérieurs utilisent ces
gates et leurs routages ; ils ne relancent ni le chercheur SAT ni des lecteurs
d'affectations historiques.

## Chaîne et fichiers

```text
Quatre fichiers primitifs inchangés
  -> constitution et histoire de rôles
  -> UnifiedMaster.publicInstance
       -> état vivant reçu
       -> contexte SAT reçu comme entrée de ce même maître
            -> production vivante partagée
            -> ouverture
            -> recherche sur les contextes
            -> code typé de transport
            -> frontière retenue + circuit configuré
            -> mémoire suivante
            -> requêtes suivantes
```

Les fichiers de production sont dans
`RelationalPerimeter/Computation/Machine/` :

- `FrontierCircuit.lean` réalise le code typé de réduction en routages et gates.
- `MasterRuntime.lean` initialise depuis le maître et raccorde la recherche,
  le circuit et le successeur.
- `MasterContract.lean` fixe le contrat combiné et son exécution partagée.
- Les autres modules portent les preuves nécessaires du contrat vivant et de
  la mémoire canonique ; leurs racines n'importent aucun test.

Les contrôles sont dans `Tests/Machine/`. La démonstration directe ancienne y
reste comme contrôle séparé, sans constituer une seconde entrée de production.

## Ce que les preuves établissent

`AcceptedFrontierCode` est indexé par les contextes sources et cibles. Ses
constructeurs d'absorption portent le témoin relationnel réellement trouvé.
Le normaliseur produit ce code dans ses branches de recherche. La
préservation est dérivée du code, non ajoutée comme champ indépendant.

Le témoin relationnel intervient dans l'évaluation du code et dans la preuve
de préservation. Les valeurs des gates sont calculées depuis les constructeurs
du code et le sélecteur ; elles ne lisent pas le témoin propositionnel effacé.
Il faut distinguer l'autorisation du transport de son incarnation configurée.

`receive_exact` épingle, pour tout `input`, tout scope, toute formule et tous
contextes reçus, la mémoire entière à la projection du maître
`UnifiedMaster.publicInstance input`. `receive_core_exact` et
`receive_problem_exact` exposent séparément le noyau et le problème initial.
Ces théorèmes publics ne sont pas limités à l'exemple d'indice zéro.

`lowerFrontier_exact` prouve, pour toute continuation typée admissible,
l'égalité entre l'action du circuit sur ses lectures et la lecture de la
continuation transportée. `ScopedProblemProduction.route_exact` raccorde cette
égalité au paquet effectivement retourné par le routage installé.
`circuit_preserves_SAT` relie séparément cette
action à la préservation du critère SAT. Ce transport n'est pas une égalité
entre les sources.

`advance_exact` raccorde le nouveau runtime au contrat riche.
`advance_frontier_is_produced` fixe la prochaine frontière sur la réduction
effective. `advance_preserves_SAT` préserve la viabilité dans les deux sens.

`all_futures_exact` porte sur toute liste finie de requêtes, avec tous les
entrelacements de reprises, lectures, impulsions, routages SAT et refus.
`run` utilise une transition appariée par requête ; le contrat à callbacks
`next` et `event` n'est que la spécification de comparaison.

Cette exactitude compare le moteur vivant riche et sa réduction, avec le même
algorithme SAT dans les deux contrats. La justesse du routage SAT est prouvée
séparément par les théorèmes d'action ci-dessus ; elle n'est pas déduite de la
seule égalité des largeurs.

## Une et deux branches sur le même maître

`Tests/Machine/MasterIntegration.lean` utilise un seul
`UnifiedMaster.publicInstance 0`, la même formule
`[[positive 12, positive 1, positive 2]]`, le même sélecteur 12 et le même
chercheur. Seule la décision reçue sur la variable 1 diffère.

Lorsque cette décision vaut vrai, la recherche retient une branche et le
circuit transporte le paquet de la branche transformée vers le slot retenu.
Lorsqu'elle vaut faux, les deux recherches dirigées échouent et deux branches
restent ; le circuit route leurs deux positions. Dans l'exemple concret, il
permute les numéros de slots 0 et 1. Tous les enfants sont prouvés
viables. L'échec du chercheur particulier n'est pas une impossibilité de toute
relation future.

Les preuves vérifient aussi que les sources restent distinctes, que les paquets
suivants utilisent le circuit produit et que tous les futurs restent exacts.

## Contrat, mémoire et largeur

Le contrat combiné ajoute les requêtes `route slot bits` et
`sampleProblem` aux requêtes vivantes existantes. Un routage est admis si
le slot source existe et si le nombre de bits respecte les permissions.
Cela n'est pas une certification SAT de tout paquet arbitraire : le théorème
sémantique concerne les lectures de continuations typées.

La frontière SAT complète reste dans la mémoire car la recherche suivante
lit ses formules résiduelles et ses décisions. La réduction vivante existante
reste appliquée au moteur. Sa minimalité sous son contrat propre ne devient
pas automatiquement une minimalité de la mémoire combinée.

`Tests/Machine/ValidAssignmentForgetting.lean` construit deux états vivants
valides dont les affectations diffèrent réellement à la variable 1, tout en
gardant génération, graine, provenance et décisions. Les mémoires reçues sont
cohérentes et ont la même observation présente. Sous la permission portant
sur la variable 2, `outside_permission_all_futures` prouve l'égalité de tous
les futurs. Sous celle portant sur la variable 1, `separating_future` exhibe
la demande `[advance]` qui les distingue. `received_distinct` prouve que les
sources n'ont pas été identifiées. Ce sont des états valides construits, pas
deux préfixes prouvés atteignables du run public ; ce résultat ne caractérise
pas la minimalité de toute la mémoire combinée.

Trois lectures doivent rester distinctes :

| Lecture | Objet mesuré |
| --- | --- |
| 2^n | Profils constitués du maître binaire |
| Frontière SAT retenue | Contextes maintenus après la recherche locale |
| Cellules de banque | Sorties finies du contrat vivant |

Les résultats exponentiels et le `iff` du maître initial sont conservés.
La nouvelle recherche SAT n'est pas présentée comme une preuve de largeur un
pour toute formule, ni comme un solveur SAT complet en temps polynomial.

## Vérification et frontière matérielle

Depuis la racine : `lake build`, puis `scripts/verify.ps1` ou
`bash scripts/verify.sh`. Les deux vérificateurs incluent le contrôle
`scripts/check-integrated-machine-codegen.py`.

Le contrôle du C compilé vérifie une production vivante et une production SAT
par reprise, et compte une invocation de leur recherche vivante commune,
même via les entrées réduites alternatives. Il ne compte pas chaque candidat
comme une nouvelle production. Il suit les champs du résultat trouvé vers
l'action, le code exécuté, le sélecteur transmis à SAT et le successeur installé
depuis la même production. Il vérifie aussi que la frontière et le circuit SAT
proviennent de l'ouverture et de la réduction reçues.

Les trois runners contrôlés sont `MasterMachine.run`, `LiveReduction.runReduced`
et `LiveReduction.ConstitutiveExecution.run`. Pour chaque trame non vide, une
paire transition fournit à la fois l'événement et le successeur de la récursion,
sur la queue effective des demandes ; la trame vide n'exécute aucune transition.
Les auto-tests de la gate protègent ces arguments, et pas seulement les nombres
d'appels. L'analyse conserve des origines distinctes par appel et par champ,
sans fusionner les marques de branches. Une forme sensible non prise en charge
est refusée explicitement. Les corps des résumés locaux sont vérifiés avant
usage ; les noyaux de recherche et de listes finies restent des frontières
explicites, non des opérations élémentaires gratuites. Les indices de formule
et les preuves propositionnelles effacés sont vérifiés par Lean, pas inventés
comme champs physiques dans le C.

L'analyse ne résume pas les modifications du tas effectuées par un helper sur
un objet reçu. Elle refuse donc ces écritures au lieu de les oublier lors du
retour : objets issus d'une production, alias, sous-champs, captures, tags et
scalaires sont concernés. Une écriture via un alias d'entrée retourné par un
helper est également refusée, car cet alias n'est pas raccordé au tas appelant.
Les helpers qui lisent leurs entrées et construisent
un nouvel objet restent acceptés. Les auto-tests incluent seize écritures
interdites, deux écritures via des alias retournés et un helper injecté dans le
runner compilé qui remplace l'événement
par `.refused` ; son rejet vient de l'écriture, pas d'un symbole manquant.
Les tags des constructeurs et les cibles des fermetures restent distincts
dans la comparaison des valeurs analysées. Cette limite explicite ne constitue
pas une analyse générale du tas C.

Pour la reprise intégrée, un précontrôle rejette une origine d'argument
indépendante sans devoir analyser toute sa représentation interne. Il ne
peut jamais valider seul : le second passage suit aussi les helpers susceptibles
d'écrire sur les objets reçus. Un contrôle sur le C réel vérifie qu'un helper
volumineux, au retour ignoré, n'échappe pas à ce second passage.

Le contrôle de routage couvre `FrontierCircuit.fire`, `Routing.apply` et
`routeProblem`, ainsi que leurs helpers transitifs et cibles de fermetures
statiquement nommées. Il rejette une dépendance SAT même sous un nom anodin,
un callback `lean_apply_*` et un symbole de projet dont le corps manque.
Les opérations de circuit fini et les interfaces de routage sont les
artéfacts autorisés ; la longueur de liste est une frontière explicite de
la bibliothèque du compilateur. Les auto-tests exigent le motif de rejet
attendu : une erreur étrangère n'est pas un test réussi.

Le partage observé dans le code compilé peut aussi résulter de l'élimination
des sous-expressions communes par le compilateur. La garantie porte sur les
appels du code généré, pas sur une absence universelle de doublons syntaxiques.
La confidentialité des constructeurs de `ScopedProblemProduction` et
`MasterHead` est un contrôle d'accès ; son rejet ne doit pas être présenté
comme une impossibilité de type indépendante. Leurs accords exacts restent
des obligations distinctes.

Ce contrôle ne prouve pas un coût physique total, une borne
globale de mémoire ni une réalisation matérielle.

Le champ inactif `Routing.targetWidth` est supprimé : la largeur cible reste
une lecture de la frontière retenue, et non une donnée imposée au routage.
La signature de ce record change ; ses consommateurs locaux sont reconstruits.

Après une modification, les contrôles directs ne remplacent pas le figement
des sources et évidences du registre. Un registre périmé doit bloquer la
publication, même lorsque les builds et contrôles compilés passent.

Ce lot est un runtime logiciel avec des circuits finis représentés par des
constructeurs. Il n'est ni un FPGA ni un nouveau matériel déjà construit.
Le routage est encore interprété structurellement ; son incarnation physique
et son coût restent des obligations séparées.
