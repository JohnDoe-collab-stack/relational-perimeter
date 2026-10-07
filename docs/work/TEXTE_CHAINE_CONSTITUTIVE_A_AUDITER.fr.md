# Calcul constitutif décomposition et machine

Dans ce cadre, la constitution relationnelle des dépendances est primitive.
Le calcul produit lui-même, pendant son exécution et à partir de ce qu'il a
déjà produit, sa décomposition opérationnelle. Les relations effectivement
trouvées, accompagnées de leurs preuves de préservation, déterminent quelles
alternatives peuvent être poursuivies ensemble. Leur regroupement n'identifie
pas les alternatives sources.

La machine donne une suite effective à cette production. Elle transforme le
code de réduction trouvé en un programme configuré qui agit sur de nouvelles
entrées. Ces entrées utilisent l'organisation produite sans recommencer la
recherche qui l'a établie. Lorsqu'une nouvelle recherche est demandée, elle
reçoit l'état et la frontière laissés par l'exécution précédente : les branches
encore poursuivies après cette étape.

La mémoire est soumise à des contrats explicites de continuation. Certaines
distinctions peuvent disparaître de sa représentation parce qu'aucun futur
de son contrat ne les observe. D'autres doivent rester distinguables parce
qu'une demande future peut encore révéler leur différence. Pour le noyau
cohérent de la machine, cette limite est caractérisée exactement, et vaut
pour toute réalisation exacte du même contrat, quel que soit son encodage.

## Des objets constitués avant leur dénombrement

Les occurrences sur lesquelles le calcul agit appartiennent à une histoire
de rôles constitutifs relationnels. Leur position, leur formation, leur source,
leur cible et leur provenance ne sont pas remplacées par une collection de
valeurs sans histoire. Les profils sont des choix d'occurrences sur cette
histoire dépendante. Leur frontière et son dénombrement sont construits
ensuite : l'extensivité est une lecture quantitative de ce qui est déjà constitué.

Le maître public fournit une exécution et un point de reprise. Les rôles,
la normalisation, les obligations et la continuation des profils sont des
consommateurs de ce même résultat. La machine reçoit ce maître, ainsi qu'une
formule SAT, des contextes constitués et des permissions de lecture déclarés
comme entrées. Ces contextes reçus ne sont pas présentés comme des sorties
de la course publique canonique.

L'initialisation est épinglée pour tout indice du maître, toute formule,
tous contextes reçus et tout scope par `MasterMachine.receive_exact`.
Les lois `receive_core_exact` et `receive_problem_exact` exposent ses deux
composantes ; cette garantie ne repose pas sur le seul exemple d'indice zéro.

## La décomposition est produite avant sa continuation

L'étape courante recherche une transformation sur les données qu'elle reçoit.
Elle applique le résultat trouvé et produit sa décomposition avant de poursuivre
depuis l'état et le contexte obtenus. La tête n'a pas de queue future dans ses
paramètres ; changer l'horizon de continuation ne change pas cette production.
La provenance et la graine produites contraignent la découverte suivante.
La temporalité désigne ici l'ordre des primitives et leurs dépendances typées.

Une transformation agit sur les continuations de la source, pas seulement
sur un exemple accepté choisi après coup. Sa preuve séparée garantit la
préservation du critère d'acceptation. Elle n'affirme ni l'égalité des sources
ni l'impossibilité de celle qui n'est plus poursuivie indépendamment. Lorsqu'un
chercheur ne fournit aucun transport, les alternatives restent séparées ;
cet échec ne démontre pas l'impossibilité de tout transport.

Dans le maître étudié, les images des sorties locales effectivement produites
composent le régime global des obligations. Deux profils sont portés ensemble
exactement lorsque leurs cibles produites sont égales, ou lorsque leurs traces
les codéterminent vers une même cible. Les sorties canoniques convergent et
leur image globale a largeur un. La réalisation de cette image possède deux
lois de retour entre représentations d'obligations ; elle ne reconstruit pas
les profils sources. La préservation sur les continuations arbitraires reste
distincte de cette convergence des sorties canoniques.

## La relation trouvée devient une action réutilisable

Une reprise de la machine produit une action vivante partagée. Le sélecteur
retourné par cette production ouvre les contextes SAT reçus. Le chercheur
compare ces contextes et construit un code de réduction dont les absorptions
portent les relations trouvées. Ce code fournit à la fois la frontière retenue
et le programme à configurer ; aucune partition ni largeur attendue n'est
passée à la recherche.

Le témoin relationnel trouvé est consommé par l'évaluation du code sur les
continuations et par la preuve de préservation. Le circuit compilé lit
l'arbre des constructeurs du code et le sélecteur, pas le témoin de preuve
effacé. Son accord avec le transport est établi séparément en Lean.

Le programme configuré agit ensuite sur des paquets contenant une position
et les valeurs des variables autorisées à la lecture. Pour toute continuation
typée de la frontière ouverte, son action donne exactement la lecture de la
continuation transportée par le code trouvé. Une autre preuve garantit que
le transport conserve SAT lorsque la continuation source satisfait SAT.
L'admission d'un paquet brut vérifie seulement sa position et sa taille ;
elle n'est pas une preuve de satisfiabilité.

Ces demandes de routage ne relancent pas le chercheur SAT et ne consultent
pas des fonctions d'affectation historiques. La reprise suivante, elle,
effectue une nouvelle recherche sur la frontière effectivement retenue.
L'état vivant suivant provient de la même production partagée. Le raccord
est orienté : le moteur vivant fournit le sélecteur à SAT ; la frontière SAT
alimente la recherche SAT suivante. SAT ne pilote pas en retour le moteur vivant.
Dans la famille vivante actuelle, la valeur du sélecteur est déterminée par
la profondeur, bien que le chemin exécuté lise le résultat de la recherche.

## Une et deux branches avec le même chercheur

Un exemple utilise le même maître public, la formule
`[[positive 12, positive 1, positive 2]]`, la même profondeur, la variable
sélectionnée 12, les mêmes permissions et le même chercheur. La décision
reçue antérieurement sur la variable 1 est la seule donnée changée.
Cette formule exige qu'au moins une des variables 12, 1 et 2 soit vraie.
Les quatre enfants ont des continuations SAT positivement construites, et
les deux enfants de chaque ouverture sont distincts.

| Décision reçue sur la variable 1 | Frontière après la première reprise | Effet du paquet `(0, [false])` | Variable de la seconde reprise | Frontière après la seconde reprise |
| --- | --- | --- | --- | --- |
| vrai | une branche | `(0, [true])` | 14 | une branche |
| faux | deux branches | `(1, [false])` | 14 | deux branches |

Dans le premier cas, la variable 1 satisfait déjà la clause : changer la
variable 12 ne détruit pas cette satisfaction. La recherche trouve la relation
qui autorise le regroupement. Dans le second, les recherches dirigées
n'obtiennent pas leur accord et les deux
branches restent. Le paquet ultérieur utilise le circuit installé dans
chaque cas ; la permutation de son numéro de position dans le second n'est
pas une identification des sources. La seconde reprise consomme la
frontière produite par la première, et la viabilité SAT est préservée
à chaque reprise. Les deux décisions initiales sont des histoires reçues
valides pour cette interface, pas deux préfixes déclarés atteignables d'une
même course canonique.

## Une mémoire exacte pour les futurs permis

Le noyau accepte des reprises de recherche, des lectures et des impulsions.
Sa mémoire réduite garde la frontière constitutive courante, les valeurs
finies autorisées, les connexions configurées et une banque normalisée.
Elle ne restaure pas l'affectation fonctionnelle complète ou les lecteurs
historiques de la mémoire de référence pour répondre aux demandes.

L'exactitude vaut pour toute liste finie de demandes, avec tous leurs
entrelacements et les refus, et pour toutes les mémoires sources du contrat.
La minimalité a un domaine distinct : pour deux mémoires sources cohérentes,
dont les connexions et les deux lectures de banque ont les tailles autorisées,
leurs projections réduites sont égales si et seulement si tous leurs futurs
observables sont égaux. Toute autre réalisation exacte du même contrat
doit conserver cette distinguabilité, sans devoir conserver ces champs
particuliers ou leur encodage. Il s'agit d'une minimalité comportementale,
pas d'un minimum d'octets.

Une impulsion de zéros révèle les connexions par leur effet, sans que leur
configuration soit ajoutée aux observations. Une reprise permet de retrouver
les valeurs vivantes encore utilisées. La nécessité est donc établie à partir
des réponses futures de la machine, pas à partir de sa représentation choisie.

Un témoin construit deux états vivants valides dont l'affectation diffère
à la variable 1, avec la même observation présente. Sous la permission de
lire la variable 2, tous leurs futurs coïncident. Sous la permission de lire
la variable 1, une reprise suffit à les distinguer. Ce témoin concerne des
états reçus du noyau ; il n'est pas présenté comme la suite du scénario SAT
ci-dessus ou comme deux préfixes publics atteignables.

La machine intégrée ajoute le routage SAT et la lecture du problème à ces
demandes. Sa réalisation préserve exactement tous les futurs finis du contrat
combiné, y compris les admissions, les événements, les observations et les
refus. Elle conserve la frontière SAT, dont la recherche suivante a besoin.
La minimalité complète de cette mémoire combinée n'est pas déduite de la
minimalité du noyau.

La continuation des profils produits et le contrat de lectures répétées de
la variable 10 après action sont également exacts dans leurs domaines propres.
Le profil source peut être irrécupérable depuis sa mémoire de reprise sans
avoir été identifié à un autre profil. Ces contrats ne sont pas confondus
avec ceux des impulsions et routages de la machine intégrée.

## Les productions sont partagées à chaque demande

L'entrée exécutable produit une paire contenant l'événement et l'état suivant.
Elle utilise cet événement et poursuit sur cet état, sans répéter la transition
pour obtenir séparément les deux résultats. La spécification à fonctions
séparées reste une référence de comparaison, pas le runner actif.
Les contrôles du code compilé suivent aussi les producteurs, les arguments
et les effets des helpers aux frontières locales annoncées.

Le circuit est encore représenté et interprété par du logiciel. La suppression
de recherches répétées sur le chemin configuré est réelle, mais elle ne rend
gratuits ni la recherche initiale, ni le routage, ni la mémoire. L'incarnation
matérielle et le coût physique total restent des obligations distinctes.

## Les largeurs sont des conséquences de ces régimes

Dans la classe binaire formalisée, la lecture extensive compte `2^n` profils
constitués. Tout régime considéré est surjectif vers ses obligations.
Sa largeur vaut exactement `2^n` si et seulement si `carry` est injective :
chaque profil reste alors une obligation distincte et séparément adressable
par le régime. Dans le maître public, `n = input + 1` ; ce même carrier
reçoit aussi le régime exécuté de largeur un, sans identification des profils.

Sur les mêmes rôles, des politiques comparatives conservant `k` rôles
séparément ont largeur `2^k`, pour `0 <= k <= n`. Leur spectre est prouvé
pour la classe de statuts concernée, pas pour tous les régimes possibles.
Elles utilisent les transports autorisés des rôles déjà produits ; elles
ne sont pas de nouvelles décisions découvertes par la recherche SAT.
Une politique non injective de largeur `2^(n-1)` existe pour chaque `n` positif.

Le résultat caractérise donc exactement la conservation de la pleine largeur
extensive comme largeur opérationnelle. Il établit aussi, par le régime
exécuté, que cette pleine largeur n'est pas imposée par la multiplicité
des profils elle-même. La largeur des profils, celle de la frontière SAT
retenue, le nombre de cellules mémoire et le coût du calcul restent
des grandeurs distinctes.

## Portée et évidence

La chaîne associe une organisation effectivement produite, son action
sur la continuation et les distinctions dont la mémoire doit répondre
sous contrat. Ses passages et leurs preuves sont détaillés dans la
[table d'évidence](PREUVES_CHAINE_CONSTITUTIVE_MACHINE.fr.md), avec la
carte des contrats et la reproduction de l'exemple. La
[version anglaise](TEXTE_CHAINE_CONSTITUTIVE_A_AUDITER.en.md) expose
les mêmes objets, hypothèses et limites.

Ce développement ne remplace pas les quatre paragraphes protégés de la
[cible canonique](../conclusion-largeur-exponentielle-conservation-identites.fr.md),
ni S1–S8 et G1–G10 du [protocole existant](ARISTOTLE_INTEGRATED_MASTER_MACHINE_AUDIT.md).
Le théorème de classe est un résultat fini général ; la recherche et la
machine décrites sont des constructions du maître et de ses contextes reçus.
Le texte ne revendique ni imprévisibilité, ni solveur SAT polynomial général,
ni borne de coût total, ni originalité établie par le seul contrôle Lean.

Ce fichier et son complément sont les documents de travail soumis à la revue
indépendante. Leur publication ne constitue pas un verdict d'audit.
Les contrats, les figures et les énoncés Lean sont inchangés. La formulation
canonique est explicitement précisée pour désigner la pleine largeur `2^n`,
et non toute croissance exponentielle. Le protocole et le verdict antérieurs
restent attachés à leur commit ; ils ne valent pas nouvel audit de ce lot.
