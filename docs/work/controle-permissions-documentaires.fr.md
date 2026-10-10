# Contrôle des permissions documentaires : parcours payé et résultat partagé

Ce document conserve la portée et les comptes du passage consacré aux
permissions. Le [passage suivant](controle-ressources-documentaires.fr.md)
ouvre les lectures des prémisses et leur consommation par la formation.
Les seuils et appels décrits ci-dessous se rapportent au passage historique ;
son relevé de vérification reste conservé avec ses empreintes d'origine.

Cet incrément poursuit D2 du [plan v0.3](RP_ALIGN_PERSIST_SPEC_v0_3.fr.md),
sur `codex/align-persist-recovery`, depuis `e291dc0d2b45880078e9c4a3b85aa0ab175bdf71`.
Il complète le [premier raccord instrumenté](controle-instrumente-documentaire.fr.md)
en ouvrant la recherche de permission jusque-là contenue dans `Deduction.execute`.
Le plan et les contrats reçus restent ceux de la v0.3 ; A conserve la priorité sur B.

Le résultat obtenu est un parcours exécutable, payé par le carburant : calcul
de la position de la règle, comparaisons des positions, visite des cellules de
permission et construction de la référence trouvée. Sa présence détermine
l'entrée dans la branche de formation ; cette référence est conservée avec
l'action effectivement formée dans la décision, puis cette décision alimente
l'étape documentaire. Les égalités avec les
fonctions d'origine accompagnent ces résultats et sont effacées à l'exécution.

## Primitives comptées

L'évaluateur garde sa convention : une transition coûte une unité, un résultat
déjà calculé coûte zéro. Les continuations sont différées jusqu'à leur paiement.
Ces unités décrivent la machine instrumentée ; leurs coûts physiques et les
allocations du runtime restent une obligation distincte.

| Étiquette | Travail déclaré |
| --- | --- |
| `referencePosition` | Examiner un constructeur de la référence reçue |
| `referenceReturn` | Construire le successeur de la position effectivement calculée |
| `naturalComparison` | Examiner un niveau des deux naturels, puis poursuivre sur leurs prédécesseurs communs |
| `permissionCell` | Examiner une cellule de la liste reçue, y compris sa terminaison vide |
| `permissionReturn` | Construire la référence trouvée ou transporter le résultat du suffixe visité |
| `deductionDecision` | Rendre la décision de refus après recherche sans permission |
| `deductionProducer` | Appeler une fois la formation existante après avoir trouvé une permission |
| `deductionAssembly` | Donner la décision reçue à l'assemblage existant |

Les deux dernières entrées ouvrent encore des appels dont le travail interne
n'est pas entièrement instrumenté. Elles comptent leurs invocations, pas leur
coût total. Le producteur de citation conserve également cette frontière.

## Position, recherche et identité

[DocumentaryControlReference](../../Tests/LocalAlignment/DocumentaryControlReference.lean)
calcule la position d'une référence typée. Son résultat porte son égalité avec
`Ref.position`. `positionTrace` construit une trace pour toute référence ;
`position_labels_bound`, `position_bounded` et `position_short` établissent son
seuil exact. La borne vaut une unité au constructeur initial, puis deux unités
par constructeur précédent : une visite et une construction de successeur.

[DocumentaryControlPermission](../../Tests/LocalAlignment/DocumentaryControlPermission.lean)
compare effectivement les naturels et parcourt la liste. Le résultat porte
son égalité avec `resolvePermission` sur cette même liste et cette même
position. La recherche s'arrête à la première occurrence correspondante.
Elle ne confond donc pas deux permissions de même valeur : `[1, 1]` rend
la référence en position `0` ; `[3, 5, 5]` recherchée pour `5` rend celle en
position `1`, sans visiter la dernière occurrence.

`referencedLookup` compose ces calculs. La recherche reçoit la position calculée
par le premier parcours. Elle n'appelle pas ensuite `Ref.position` pour refaire
ce calcul. Le transport de la référence par l'égalité de positions est effacé,
et conserve les données effectivement trouvées.

La comparaison descend les naturels par leurs successeurs communs. Ainsi,
comparer `32` à `32` prend 33 transitions de comparaison. Cette convention
structurelle doit être conservée ou remplacée explicitement lors du choix
de représentation et d'enveloppe de D3 ; aucune borne en taille binaire n'est
établie ici.

## Bornes établies sans supposer la réussite

L'évaluateur dispose désormais de `Within` et de lois de composition de bornes.
Un témoin de `Within code bound` contient une trace finie dont la longueur ne
dépasse pas cette borne ; `within_complete` prouve que l'évaluateur atteint
effectivement son résultat à ce carburant. Les bornes s'ajoutent lorsque le
résultat du premier calcul est transmis au suivant.

La borne de permission est définie depuis les entrées, sans recevoir un résultat
de recherche : pour la liste vide, elle vaut `1` ; pour une tête et un suffixe,
elle ajoute le coût de comparaison de cette tête, la borne du suffixe et deux
transitions de visite et de retour. `lookup_bounded` la démontre pour toute liste
finie et toute position. `lookup_within` en déduit la terminaison à cette borne.
`referenced_bounded` y ajoute le parcours payé de la référence reçue.

Cette borne est une majoration. Avec `[1, 1]` et la position `1`, elle vaut `9`
alors que la recherche s'arrête après `4` transitions. Un carburant inférieur
à une majoration peut donc suffire. Les tests d'insuffisance utilisent le coût
exact des traces, conformément à `T20_BOUND_INTEGRITY`.

Ces lois portent sur les transitions déclarées. La construction de leurs
bornes, la représentation des naturels, le bootstrap et les ressources mémoire
doivent encore être instrumentés et bornés pour fermer D3 et P15.

## Raccord au producteur et au présent

[DocumentaryControlDeduction](../../Tests/LocalAlignment/DocumentaryControlDeduction.lean)
reçoit les ressources et les références effectivement lues dans le présent.
La permission absente produit un refus. La permission présente autorise
l'appel à `Deduction.form`, dont l'action et la référence trouvée constituent
la décision. `actual_decision` établit son égalité avec `Deduction.execute` ;
la fonction d'origine n'est utilisée que dans cette preuve.

[DocumentaryControlStep](../../Tests/LocalAlignment/DocumentaryControlStep.lean)
transmet ensuite cette décision à `Program.deductionStep`. Le paquet reste
égal à `Program.step` sur le cadre et l'instruction reçus. Son certificat de
complétude consomme le champ de progrès de ce paquet, sans rejouer le producteur.
Le reset et les projections mémoire déjà raccordées conservent ce calcul.

Sur les cas du maître existant, les seuils deviennent `10` transitions pour la
différence, `17` pour la somme et `19` pour la règle interdite. La somme conserve
la valeur `2` et les origines `[1, 2, 1, 2]`. Le refus garde son statut ; les
prémisses absentes et la demande erronée restent des cas exécutables distincts.
Une citation garde son seuil de deux transitions à sa frontière actuelle.

## Vérification et portée

Le [client d'exécution](../../scripts/run-documentary-interpreter-smoke.py) passe
240 verdicts de carburant sur les étapes documentaires, 234 sur les permissions,
72 sur les positions et neuf contrôles d'intégration. Il utilise des attentes
littérales pour les seuils, traces, identités, valeurs, origines et événements.
Ses 16 audits sont sans axiome. Les permissions couvrent la liste vide, les
doublons, une occurrence tardive, l'absence et les comparaisons plus longues.

Le [contrôle du C produit](../../scripts/check-documentary-interpreter-codegen.py)
passe aussi. Il examine les corps nommés et leurs liens de continuations :
paiement avant entrée, position calculée transmise à la recherche, permission
conservée avec l'action formée dans la décision, décision transmise à
l'assemblage et certificats consommateurs. Trente mutations textuelles de ces
corps sont rejetées. Ce sont des fixtures du contrôleur, pas des programmes
mutants compilés ni une preuve du graphe physique complet.

La gate complète `scripts/verify.ps1` a réussi sur **305 fichiers Lean** :
25 777 constantes dans 304 modules, 364 exceptions générées par le compilateur,
aucun axiome écrit et 23 fixtures de refus conformes. Les 113 audits explicites
des sept modules de contrôle sont sans axiome. Les sources Lean sont restées
inchangées pendant cette vérification ; la chaîne locale comprend 184 modules.

Le [relevé propre à ce passage](controle-permissions-documentaires-verification.json)
conserve les commandes, résultats et empreintes du nouvel arbre. Le relevé du
premier passage garde ses empreintes historiques. La revue locale porte sur
les énoncés complets et leurs dépendances ; aucun audit indépendant ou essai
confirmatoire de modèle n'est attribué à cet incrément.

## Suite de D2

Le prochain travail doit ouvrir les lectures de ressources, la formation,
les opérations sur entiers, le maître de citation et les assemblages, en
faisant consommer leurs résultats effectivement calculés. Il faut aussi fermer
les coûts de composition, de trace et d'allocation. D2 entier, D3, CONT-03 et P15
restent ouverts à ces frontières. Ensuite viennent le secours D4, l'activation
complète A1, les transactions A2, leur réalisation A3 et l'évaluation locale.
