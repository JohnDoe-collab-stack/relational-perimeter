# Application de RP-ALIGN-PERSIST-01 v0.3

La [spécification v0.3](RP_ALIGN_PERSIST_SPEC_v0_3.fr.md) est conservée dans son
texte reçu, avec fins de ligne LF. Ce document fixe les choix de réalisation,
qualifie le socle actuel et suit leur application. Il ne remplace ni la
spécification, ni le [plan documentaire existant](plan-alignement-agent-dossier.fr.md).

La demande du 10 octobre 2026 autorise l'enregistrement du plan et le début
de son application, en conservant la priorité A avant B. La demande suivante
autorise une branche dédiée et le commit de ce seul incrément.

## Socle et portée du premier incrément

Le socle qualifié provient de `codex/ai-alignment-under-contract`, au commit
`6cf87612cae3820be8ad3d9d4229bf26a37e4330`. Son arbre suivi était propre
avant l'enregistrement du plan. Cet incrément est maintenant isolé dans
son propre worktree, sur `codex/align-persist-recovery`, depuis ce même commit.
Les modifications du chantier parallèle ne sont pas reprises dans cette branche.

La référence historique `f30196e4…` de la spécification reste inchangée.
Le nouveau socle ajoute les codecs de constitution, histoire, génération et
état transmis entier, puis l'assemblage typé du présent. Le
[rapport de cet incrément](etat-maitre-et-checkpoint-assemble.fr.md) garde
sa provenance de développement ; ses résultats ne sont pas réétiquetés.

| Passage | Situation au nouveau socle | Obligation restante |
| --- | --- | --- |
| Programme reçu et accomplissement | Instructions typées, permissions et lois primitives ; accomplissement adaptatif déjà prouvé | Exposer le secours obligatoire et sa validité depuis ces données |
| Contrôle documentaire | Codec de la file, des liaisons, du contexte, du compteur et du résumé | Activation instrumentée avec borne de contrôle |
| État transmis maître | Octets de l'assignation, du lecteur, de la génération, de la graine, des décisions et de la provenance | Autres valeurs et environnements maître |
| Présent assemblé | Égalité du présent avec payload maître typé conservé ; futurs déclarés transportés | Fichier autonome du curseur et du présent entiers |
| Effets durables | Expériences de composants existantes | Nouveau protocole transactionnel, phases et vivacité |
| Modèle | Qwen local déjà raccordé au noyau Agent | Interface documentaire, puis comparaison du lot 7 |

La qualification comporte les lectures des instructions, de la procédure,
des entrées pertinentes du registre et des producteurs/consommateurs employés.
Le relevé [de cette application](application-alignement-persistant-verification.json)
identifie les commandes réellement exécutées et le snapshot de développement.
Les évidences historiques du registre ne sont pas modifiées.

## Choix fixés avant les expériences

### Exécution obligatoire en fenêtre complète

La première incarnation ne découpe pas le secours en tranches. Une fenêtre
de service obligatoire permet de terminer le contrôle borné. Un watchdog
signale une indisponibilité ; il ne recommence pas indéfiniment un calcul
valide avec un délai insuffisant. La réservation du service, de la mémoire
et du stockage relève du raccord runtime à établir, pas d'un nombre seul.

Le traitement facultatif du modèle est isolé et limité. Son abandon dispose
de ses propres moyens ; il ne consomme pas la réserve du secours. Les
réponses périmées sont rejetées. Les tranches reprenables restent une
extension possible après preuve du raffinement prévu par la spécification.

La garantie retenue porte sur une allocation obligatoire disponible à chaque
reprise sous le service déclaré. Les recalculs avant commit et les retries
ont des comptes séparés. Une réserve cumulée finie pour un nombre illimité
d'interruptions ne fait pas partie de cette réalisation ; elle demanderait
une borne des fautes ou un approvisionnement externe supplémentaire.

### Coût dépendant de l'état

Le contrôle sera instrumenté sur une représentation finie des instructions
et de leurs environnements. Sa borne est calculée avant l'appel, depuis le
présent conservé. Les traversées de références, tailles des entiers, accès,
validations et auxiliaires sont identifiés et leurs coûts composés.

Le calcul de la borne et l'activation ont leurs propres bornes structurelles.
Le carburant facultatif, le contrôle obligatoire et le quota métier sont
trois comptes. Les moyens du successeur préparé doivent être couverts avant
incorporation. Aucun plafond de temps universel n'est déduit du rang.

Le premier raccord des données de reprise mesure des opérations sémantiques
documentaires. Il ne ferme pas le contrôle instrumenté : compter une citation
comme une étape ne borne pas ses calculs internes ni son coût physique.

### Stockage local transactionnel unique

La première réalisation d'A2/A3 utilisera une base SQLite unique, un écrivain,
`journal_mode=DELETE`, `synchronous=EXTRA` et une transaction explicite pour
chaque unité de validation. La bibliothèque reçue sur ce poste rapporte
SQLite `3.53.1`. Les paramètres doivent être relus et vérifiés à l'ouverture.

Le même commit conservera génération, checkpoint, phase, paquet publié,
consommations et reçu. Les lecteurs métier passeront par cette base et le
protocole de génération. Une copie exportée sur disque possède un statut
distinct tant que sa fidélité et sa livraison ne sont pas raccordées.

La publication atomique visée est celle des octets exacts dans le domaine
local reçu. La comparaison du doublon validé précède le rejet de génération.
Après une erreur ambiguë, l'adaptateur relit le reçu avant toute répétition.

Les garanties de SQLite reçoivent notamment le verrouillage correct et la
durabilité réelle des primitives du système et du support. La
[documentation de commit atomique](https://sqlite.org/atomiccommit.html)
explicite ces hypothèses ; le
[réglage synchronous](https://sqlite.org/pragma.html#pragma_synchronous)
décrit le mode EXTRA en journal DELETE. Le noyau Lean ne prouve pas SQLite,
le système d'exploitation ou le matériel. Le modèle A2 et son raccord aux
transactions restent à réaliser ; ce choix technique ne les déclare pas clos.

### Modèle local conservé

Le raccord A4 conserve le modèle reçu Qwen3 4B, sa révision et sa
quantification décrites dans le [README de l'application](../../apps/local-alignment/README.fr.md).
Les paramètres d'inférence et le protocole documentaire seront gelés avant
l'essai confirmatoire. Le modèle fournit des propositions ; aucune voie
indépendante d'effectuation ne lui est ajoutée.

## Ordre des preuves et jalons

| Ordre | Travail | Clôture exigée |
| --- | --- | --- |
| A0 | Qualifier la révision reçue et ses dépendances | Révision existante, lectures et vérifications rapportées |
| D1 | Relier les données de continuation reçues au secours réel | Validité primitive séparée du calcul ; paquet partagé et progrès |
| D2 | Construire l'interprète instrumenté | CTL-SOUND, CTL-COMPLETE et CTL-MONO |
| D3 | Calculer et protéger les enveloppes | Bornes du contrôle et du bootstrap, isolement, fermeture des successeurs |
| D4 | Composer les tours | Secours dans sa borne, paquet réel, progrès et fermeture |
| A1 | Charger toutes les ressources maître et le présent | Couverture positive, octets, activation et reprise utilisable |
| A2 | Formaliser les phases et transactions | Avant/après commit, doublons, ressources et vivacité primitive |
| A3 | Raccorder les opérations physiques | Processus neuf, nouvelle citation et déduction, publication et interruptions |
| A4/A5 | Raccorder Qwen et comparer | Protocole figé, évaluateur indépendant et résultats complets |
| B | Ajouter les ressources consommables | Seulement après clôture d'A ; budgets 1/2/3 et voies distinctes |

D1 prolonge les recettes documentaires existantes. D2 à D4 doivent
instrumenter leurs contrôles réels ; un petit interprète sans raccord aux
producteurs ne ferme pas leurs obligations. A1 réutilise ces lois pour
l'activation et ne remplace pas le maître par une nouvelle instance.

## Premier raccord : données de reprise documentaire

Le module [DocumentaryRecoveryData](../../Tests/LocalAlignment/DocumentaryRecoveryData.lean)
emploie le présent documentaire existant. Ses données exécutables sont la
file réellement conservée. Sa validité utilise l'admissibilité primitive
des instructions et les réalisations des liaisons déjà produites.

Le secours appelle la transition mémoire existante avec une politique
silencieuse. Il ne reçoit pas la preuve de validité pour choisir son action.
Son paquet expose cette transition et son successeur, sans réexécuter le
producteur pour fabriquer une sortie équivalente.

Le certificat d'accomplissement reçoit explicitement le résultat et la trace
déjà produits. Le contrôle du code compilé vérifie deux sites directs de
production et l'absence de ces appels dans quatre fonctions de certificat ;
il refuse deux duplications et quatre injections de rejeu. Sa portée porte
sur les corps nommés, complétée par les gates mémoire et adaptative existantes.

Les obligations de ce premier passage sont : conservation de la validité,
baisse du rang lorsque la file est non vide, conservation des anciennes
liaisons, accomplissement de la file admissible et transport du calcul après
projection, reset et chargement du composant de contrôle.

Les [cas de raccord](../../Tests/LocalAlignment/DocumentaryRecoveryDataCases.lean)
consomment la racine documentaire existante, un préfixe réel et un checkpoint
assemblé. Un programme interdit reste représentable et son résultat manque
le but ; aucune validité forte n'est cachée dans son état de base.

### Carte des quatre dépendances

| Lecture | Dépendance effectivement employée |
| --- | --- |
| Formation | File typée, ports reçus, occurrences et formations du présent existant |
| Exécution | `Memory.step`, `Adaptive.takeTurn`, `Program.step` et leurs producteurs partagés |
| Preuve | `Snapshot.Accomplishable`, admissibilité primitive et trace réelle de l'exécution |
| Transport | Projection mémoire, reset du contexte et égalité du présent chargé dans la portée existante |

Ce passage commence CONT-02 et le raccord sémantique de D1. P15, la borne
instrumentée complète de CONT-03, le chargement autonome du présent, les
transactions et la vivacité physique restent ouverts. A et B ne sont pas
déclarés terminés par ce premier incrément.

## Qualification et vérifications

La gate complète du socle `6cf8761…` a réussi : 296 fichiers Lean,
25 352 constantes dans 295 modules, aucun axiome écrit, 23 fixtures de
refus conformes et toutes les vérifications documentaires et d'exécution.
Les 364 exceptions recensées concernent les déclarations produites par le
compilateur déjà encadrées par l'audit exhaustif.

Les deux nouveaux modules compilent avec 49 audits explicites sans axiome.
Le client de test exécute 23 contrôles avec attentes littérales : début,
préfixe réel, reset, deux histoires effectivement oubliées, contrôle chargé,
checkpoint assemblé et programme interdit. Ses six audits sont sans axiome.
Le chargement de contrôle reçoit encore le même dossier et stockage ;
l'assemblage reçoit encore le payload maître typé.

Des fichiers de portabilité sont développés en parallèle dans ce checkout.
La vérification finale de cet incrément utilise donc une copie figée du
socle et de ses seuls changements, avec l'audit exhaustif correspondant.
Ce contrôle ne qualifie pas les modifications simultanées des autres travaux.
Le relevé JSON conserve les commandes, empreintes et résultats effectifs ;
aucune nouvelle évidence n'est inscrite au registre avant une révision
de livraison existante.

La gate complète de cette copie a réussi : **298 fichiers Lean**, 25 438
constantes dans 297 modules, 364 exceptions générées et **aucun axiome écrit**.
Les contrôles documentaires, les tests d'exécution et de reprise, les contrôles
du partage compilé et les 23 fixtures de refus ont passé. Les changements
de code qualifiés sont identifiés par leurs empreintes dans le relevé.

Un [second incrément](controle-instrumente-documentaire.fr.md) commence D2 :
l'évaluateur possède les preuves CTL-SOUND, CTL-COMPLETE et CTL-MONO ;
la lecture des liaisons est payée et raccordée aux producteurs documentaires.
Le paquet instrumenté est celui de l'étape reçue et son certificat consomme
le résultat effectif. Les coûts internes des producteurs et assemblages
restent à instrumenter avant de fermer D2 entier, puis les bornes et
enveloppes de D3 et le secours borné de D4.

Le [passage suivant de D2](controle-permissions-documentaires.fr.md) instrumente
le calcul de position de la règle et la recherche de permission, avec une borne
démontrée depuis leurs entrées. La permission trouvée détermine l'entrée dans
la formation et reste dans la décision consommée par l'assemblage existant.
Les doublons conservent la première identité trouvée ;
le refus et la somme conservent leurs résultats et leurs témoins. Le coût interne
de la formation, du maître et des assemblages reste ouvert dans ce passage.

Le [raccord des lectures de ressources](controle-ressources-documentaires.fr.md)
poursuit D2 : chaque cellule parcourue est payée, puis les deux valeurs lues
alimentent une seule opération. La formation conserve le producteur existant
et la formation antérieure ; son égalité avec l'action d'origine est démontrée.
La différence coûte désormais 13 transitions et la somme 21 dans les cas du
maître. Le refus à 19 transitions ne lit aucune ressource de prémisse.
Les opérations sur entiers, la construction du producteur, le maître de
citation et les assemblages restent à ouvrir, ainsi que les coûts de
composition, de trace et d'allocation. D2 entier, D3 et D4 restent ouverts.

Le [raccord du producteur](controle-producteur-documentaire.fr.md) poursuit
D2 en conservant la position déjà calculée pour la permission, puis en payant
les positions des deux prémisses et huit étapes de construction du producteur.
Ses ports restent les références reçues dans leur ordre. La formation appelle
l'opération de ce producteur sur les deux valeurs lues et conserve ce même
producteur dans son témoin positif. L'égalité avec l'action d'origine porte
sur l'action entière. Les seuils des cas du maître passent à 25 pour la
différence et 35 pour la somme ; le refus reste à 19.
L'opération sur entiers, les autres constructions de formation, le maître,
les assemblages et les coûts de composition, trace et allocation restent
à instrumenter. D2 entier, D3 et D4 restent ouverts ; A précède toujours B.

Le [calcul entier et la formation de déduction](controle-calcul-formation-documentaire.fr.md)
consomment désormais le code d'opération conservé dans le paquet du producteur
et les valeurs lues. Une interprétation constructive, valable pour tous les
entiers reçus, produit le résultat sous carburant ; quatre étapes distinctes
assemblent les valeurs, le témoin positif, le support et l'action. Le code
compilé conserve ce résultat, le producteur effectif et la formation antérieure.
La réalisation arithmétique est unaire, avec borne dépendant des valeurs.
Les seuils des exemples passent à 74 pour la différence et 44 pour la somme.
Le maître de citation, sa formation, les assemblages et les coûts de composition,
de trace et d'allocation restent ouverts. Le transport d'extension dans
l'assemblage de déduction reste aussi à raccorder. D2 entier, D3, D4, CONT-03
et P15 ne sont pas déclarés clos.

## Relecture du plan et assemblage de déduction

La confrontation à CTRL-02 et à l'annexe D confirme l'ordre : finir le contrôle
de D2, puis son bootstrap et ses enveloppes en D3, puis les tours en D4.
Les lois générales de l'interprète existent ; leur raccord à toutes les opérations
du secours reste la condition de clôture. A conserve la priorité sur B.

Le [nouvel assemblage de déduction](controle-assemblage-deduction.fr.md) traite
les références de positions, le type de sortie, la connaissance incorporée,
le stockage, l'extension, la sortie, la frame et le paquet d'étape. Le transport
emploie le type effectivement construit et le support de l'action conservée.
Le certificat de progrès consomme la sortie et l'extension de ce même paquet.
Le chemin instrumenté ne reconstruit plus le producteur pour ce transport.

| Passage de D2 | État après cet incrément |
| --- | --- |
| Permission, références, prémisses, producteur | Instrumentés dans la portée documentaire reçue |
| Calcul entier et formation de déduction | Instrumentés ; réalisation arithmétique unaire |
| Construction de l'assemblage de déduction | Instrumentée depuis la frame reçue ; mêmes étape et progrès |
| Maître de citation et formation des citations | À instrumenter en conservant le maître et ses productions |
| Assemblages de citation et d'entrée manquante | À décomposer |
| Restauration de frame et appels différés de liaisons/justification | Coûts encore à raccorder |
| Composition, traces, paquets de l'interprète et allocations | Modèle complet encore à construire |

Les seuils documentaires deviennent 87 pour la différence, 61 pour la somme
et 23 pour le refus. Les lectures de position supplémentaires de l'assemblage
sont réellement exécutées et comptées ; aucun gain de coût n'est revendiqué.
Le relevé courant est celui du nouvel assemblage ; les relevés précédents
restent attachés à leurs arbres vérifiés. D2 entier, D3, D4, CONT-03 et P15
restent ouverts.

La gate complète de cet incrément a réussi sur 310 fichiers Lean et 26 024
constantes. Les deux smokes du contrôle produisent 6 659 verdicts ; les gardes
C rejettent 256 mutations textuelles. Les empreintes Lean et des contrôles
restent celles figées avant le run. Ces vérifications qualifient cet incrément
et conservent les obligations ouvertes du tableau.

## Première ouverture du maître de citation

Le [raccord des contrôles de source](controle-maitre-citation.fr.md) ouvre
la recherche documentaire du même maître. Ses contrôles gauche et droit
emploient les positions payées, la première permission trouvée et les passages
effectivement lus. Les comparaisons structurales portent sur le fait, la valeur
et l'origine éventuellement imposée. Une source sans permission n'est pas lue.

Les deux contrôles produits déterminent la formule réellement ouverte ; la
tête, l'ouverture et la réduction effectivement produites sont conservées
dans l'étape. Le chemin instrumenté ne relance pas `Dossier.step` pour fabriquer
son paquet ou son certificat. Les égalités portent sur l'étape entière.

| Passage du maître | État de cet incrément |
| --- | --- |
| Positions, permissions et lectures des deux sources | Instrumentés et bornés dans le catalogue déclaré |
| Comparaisons du fait, de la valeur et de l'origine | Instrumentées, sans comparaison naturelle native cachée |
| Transmission des contrôles à la formule et à l'étape | Raccordée aux productions effectives |
| Production interne de tête, ouverture et normalisation | Appels complexes nommés ; calculs internes encore à ouvrir |
| Complétion, extraction et formation de citation | Appel complexe nommé ; calculs internes encore à ouvrir |
| Assemblage de citation, entrée manquante et administration | D2 reste ouvert, ainsi que les coûts différés et allocations |

Les seuils du catalogue actuel sont 83 pour la citation de référence, 82 pour
le refus avec origine interdite et 150 pour la citation révisée. Ces seuils
incluent encore des appels complexes à une transition ; ils ne bornent pas
le coût interne du maître ni le coût physique total. Leur hausse décrit
l'ouverture des contrôles auparavant cachés, sans revendication de gain.

Le [relevé de développement](controle-maitre-citation-verification.json)
conserve la portée et les résultats de cet incrément. Les relevés précédents
restent historiques. D2 entier, CONT-03 et P15 ne sont pas déclarés terminés ;
D3 puis D4 suivent toujours la clôture complète de D2, et A précède B.

La gate complète de cette ouverture a réussi : 312 fichiers Lean, 26 099
constantes, aucune exception écrite, 7 459 verdicts d'exécution et 318 mutations
textuelles rejetées. Les 189 audits explicites des quatorze modules de contrôle
sont sans axiome. Ces résultats qualifient les contrôles et transmissions
décrits, sans fermer les calculs internes encore nommés dans le tableau.

## Décision et formation effectives de la citation

Le [raccord de complétion](controle-completion-citation.fr.md) poursuit D2.
La décision lit la continuation réellement retenue ; son assignation produit
le bit qui choisit l'occurrence contrôlée. L'extraction consomme une lecture
payée de cette occurrence et conserve le même producteur et la formation
antérieure. Le readout formé, sa permission et son incorporation alimentent
le paquet complet. L'égalité avec les producteurs d'origine inclut le témoin
d'accomplissement en `Type` et le raccord à l'étape du programme.

Un majorant conservateur de décision provient des deux références reçues.
Il est démontré sans lancer la recherche du maître pour calculer son
allocation : la normalisation ne fait pas croître la longueur de la frontière,
l'ouverture reçue a deux branches et le candidat vient d'une des deux
occurrences. Le coût du calcul de ce majorant reste une obligation de D3.

| Passage de D2 | État courant après cet incrément |
| --- | --- |
| Contrôles des sources et transmission à la recherche | Instrumentés ; même tête, ouverture et réduction |
| Lecture de continuation, sélection et extraction | Instrumentées depuis les données réellement retenues |
| Formation, readout, admission et paquet de complétion | Raccordés aux productions originales, avec majorants du catalogue |
| Découverte de tête, ouverture et normalisation | Calculs internes encore à ouvrir |
| Préservation, routage et application des fonctions d'assignation | Frontières distinctes nommées ; calculs internes et appels différés ouverts |
| Assemblage de citation et d'entrée manquante | À décomposer |
| Restauration de frame, lectures différées, composition, traces et allocations | À instrumenter dans le modèle complet |

Les seuils documentaires actuels sont 106 pour la citation de référence,
84 pour le refus à origine interdite et 176 pour la citation révisée.
Ils comptent encore les frontières complexes indiquées. Les gardes C et les
matrices de carburant contrôlent la fidélité des productions et du compteur
déclaré ; elles ne ferment pas le coût physique ou le contrôle de tous les
successeurs.

Le [relevé courant](controle-completion-citation-verification.json) qualifie
cet incrément. Les relevés antérieurs restent historiques. D2 entier,
CONT-03 et P15 restent ouverts ; D3 puis D4 suivent sa clôture complète,
et A conserve la priorité sur B.

La gate complète de cet incrément a réussi après correction des preuves
arithmétiques des majorants : 314 fichiers Lean, 26 229 constantes, aucune
exception pour une déclaration écrite, 224 audits explicites de contrôle
sans axiome, 8 959 verdicts d'exécution et 427 mutations textuelles rejetées.
La qualification conserve l'échec d'audit initial et la correction, sans
changement des définitions exécutées ni des attentes de traces.

La prochaine ouverture concrète concerne `VariableMaster.masterHead` :
`discover`, `applyStage`, `decompose`, `assemble`, puis
`continueWithReferences`. Chaque passage doit transmettre le support
effectivement constitué au suivant et conserver l'égalité du paquet entier,
dont la tête, le curseur suivant et les formations. L'ouverture de ces
producteurs devra aussi couvrir leurs calculs internes ; leur seul
séquençage ne fermerait pas D2.
