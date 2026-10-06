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
restent ; le circuit conserve leurs deux slots. Tous les enfants sont prouvés
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

Le contrôle du C compilé vérifie les producteurs locaux nommés : une production
vivante et une production SAT par reprise, une ouverture, une normalisation
et une configuration par production SAT, et une transition par requête.
Il interdit la recherche SAT et les callbacks d'affectation dans le chemin
des paquets configurés. Il ne prouve pas un coût physique total, une borne
globale de mémoire ni une réalisation matérielle.

Ce lot est un runtime logiciel avec des circuits finis représentés par des
constructeurs. Il n'est ni un FPGA ni un nouveau matériel déjà construit.
Le routage est encore interprété structurellement ; son incarnation physique
et son coût restent des obligations séparées.
