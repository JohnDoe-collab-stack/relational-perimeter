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
| D2 | Construire l'interprète et couvrir le chemin documentaire réel | Clos le 12 octobre 2026 après suite complète et revue indépendante. CTL-SOUND, CTL-COMPLETE, CTL-MONO ; producteurs, lecteurs et administration effectivement raccordés ; [reçu autonome](cloture-d2-verification.json) |
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

### Correction de pilotage et clôture de D2

La demande du 11 octobre 2026 exige la clôture entière de D2 sous supervision.
Le [dossier de clôture](cloture-d2.fr.md) fixe désormais ses critères, les
entrées effectives, l'inventaire et les validations nécessaires. Les comptes
rendus ci-dessous restent historiques ; leurs listes de reste mêlaient
parfois instrumentation, budgets et activation.

`D2` désigne le jalon de ce tableau. La section D.2 de l'annexe de la
spécification regroupe aussi `BOUND-COMPUTABLE` : dans cet ordre de travail,
le calcul des enveloppes et le bootstrap correspondant relèvent de D3.
La conservation de recettes de lecteurs utilisables relève déjà du raccord
de D2 ; leurs codecs complets, leur activation depuis des octets et son coût
relèvent d'A1 et des obligations de reprise. D4 compose les tours et établit
le secours commun dans son allocation. Cette répartition conserve toutes
les obligations de la spécification.

Les cinq critères du dossier de D2 sont maintenant qualifiés ensemble, avec
réception racine et indépendante de la suite complète réellement terminée.
D2 est clos après mise à jour documentaire, vérification des liens et du diff.
L'inventaire porte sur les chemins effectivement appelés, y compris les
closures différées et l'administration. L'instance concrète forme et conserve
ses entrées, les transmet à ses vrais consommateurs et ferme les conditions
de ses interfaces. Les recettes sont maintenues depuis l'état initial général
et par tous ses constructeurs de successeurs.

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

## Ouverture de la tête et des assemblages

Le [raccord suivant](controle-tete-assemblages.fr.md) exécute la chaîne des
sept productions du même maître et conserve le paquet `MasterHead` entier.
Il ouvre génération, extraction, filtrage de provenance, parcours des
candidats et assemblages de leurs compteurs. Il ouvre aussi les tentatives
entières : fraîcheur, résidus, enfants, transformations et comparaisons de
formule et d'histoire, puis la recherche de relation sur ces endpoints réels.
Les assemblages de citation et
d'entrée manquante sont décomposés et raccordés à l'étape originale entière.
L'application ouvre le schedule stocké, ses deux recherches, le transport
composé, le stade et l'assemblage du successeur. La décomposition conserve
les deux occurrences et leurs constitutions, puis exécute la collecte des
sorties et la déduplication de leur image. Ces constructions alimentent le
support réel ; leurs accords portent sur les paquets entiers.
La voie `ControlStep.expandedCode` consomme cette tête et paie sa restauration
de frame ; l'administration de l'évaluateur source possède son propre
résultat et sa preuve de terminaison.

| Passage de D2 | État courant de la voie étendue |
| --- | --- |
| Génération, extraction, provenance et tentatives | Instrumentées, résultats entiers et endpoints conservés |
| Application et décomposition | Schedules, recherches, transport, stade, successeur, licence et image construits depuis les résultats réels ; générateur constitutif, ouverture du rôle et formations internes encore ouverts |
| Kinds dépendants et arguments de métadonnées | Douze sites de lectures natives de tête et deux sites d'endpoints de schedule révélés par le C ; coût encore ouvert |
| Ouverture, normalisation, préservation, routage et assignation | Obligations internes antérieures toujours ouvertes |
| Assemblages de citation et d'entrée manquante | Décomposés, même étape et même progression |
| Restauration et lectures différées | Frame et table contrôlées ; lecteurs vide/citation/déduction et recettes de transports fermés ; raccord complet aux frames et codecs encore ouvert |
| Composition, traces et allocations abstraites | Évaluateur source construit ; migration de tous les callbacks et enveloppes encore à établir |

Le protocole courant comporte 31 contrôles d'intégration et seize
audits runtime ; les gardes C ciblées rejettent 683 mutations textuelles.
Les seuils 2, 5 et 18 des trois formes de transport sont vérifiés par le
noyau, avec expiration à une unité en moins. Deux des quatre reconstructions
natives de schedule apparues dans ce raccord sont supprimées ; deux sites
d'indices exécutables d'endpoints restent à remplacer par un cache payé.
Le relevé intermédiaire
de 23 104 transitions est historique : l'intérieur des tentatives n'était
pas encore instrumenté. Le plafond de test n'est pas
présenté comme une borne de bootstrap. Les API et relevés antérieurs restent
historiques ; le secours de `RecoveryData.prepare` n'est pas encore remplacé.

La [qualification locale](controle-tete-assemblages-verification.json) expose
les réparations de développement, les limites et les vérifications de cette
révision. La gate complète a réussi sur 337 fichiers Lean : 27 371 constantes,
aucune exception pour une déclaration écrite, 486 audits explicites des
modules de contrôle sans axiome et 23 fixtures d'échecs attendus. Les 31
contrôles runtime et leurs seize audits ont passé sur ce même arbre.
**La demande entière et D2 restent ouverts.** La prochaine
fermeture doit traiter le générateur constitutif et l'ouverture du rôle,
avec l'intérieur des formations, la représentation payée des métadonnées
et les autres moteurs et lecteurs listés. D3 et D4 ne sont pas déclarés commencés
par cet incrément ; A conserve sa priorité sur B.

## Génération constitutive, occurrences et bornes locales

Le [passage suivant](controle-generation-roles-bornes.fr.md) remplace
l'appel atomique du générateur constitutif par la construction de sa couche,
de sa cible et de ses lois, consommées dans le paquet original entier.
Il raccorde la formation des deux occurrences aux endpoints du schedule
effectivement produit, puis leurs évidences à la licence exécutée.
Les deux reconstructions natives d'endpoints restantes sont supprimées
du transport et de la formation de son lecteur.

Le compte structural `o` du code de frontière donne une borne locale
`o + 31` au générateur. Le calcul contrôlé de cette allocation lit seulement
le code reçu et possède sa propre borne `b + 64`. La preuve consomme
l'allocation calculée avant l'exécution du générateur. Ces majorants locaux
préparent la fermeture ; ils ne sont pas l'enveloppe de tout le secours.

La gate complète passe sur 342 fichiers Lean, avec 27 554 constantes,
aucune exception pour une déclaration écrite et 552 audits explicites des
modules de contrôle sans axiome. Les 31 contrôles d'intégration, les quatre
histoires du bootstrap et les 842 mutations textuelles des gardes C passent.
La [qualification](controle-generation-roles-bornes-verification.json) conserve
les empreintes de cet arbre ; les qualifications antérieures restent
historiques. Les douze sites de lectures natives des
métadonnées de tête, les autres indices exécutables, les moteurs documentaires,
les lecteurs différés et l'administration complète restent à fermer en D2.
Les enveloppes obligatoires et successorales de D3 et le raccord borné de D4
au présent conservé et rechargé restent à implémenter. A conserve sa priorité
sur B.

## Arguments et métadonnées de tête conservés

Le [raccord suivant de D2](controle-metadonnees-tete.fr.md) conserve les arguments
effectivement lus, forme les indices dans le contrôle et transmet les supports
entiers aux sept producteurs du maître. Les références suivantes utilisent
ces arguments et ces indices conservés. Les douze sites de lectures natives
de métadonnées de tête recensés précédemment sont supprimés du C de tête.
La garde rejette leur réintroduction dans les modules de tête et de formation
conservée, ainsi que la perte des arguments, de l'indice ou du support positif.

Les preuves conservent l'égalité au paquet maître entier, avec sa tête, son
curseur suivant et l'accord de sa frontière. Les lois de lecture établissent
que la nouvelle occurrence lit la valeur produite et que les références
antérieures conservent leur lecture. La formation conservée possède une borne
locale composée, conditionnelle aux bornes fournies de ses codes d'indice et
d'opération ; l'enveloppe globale demeure une obligation de D3.

La gate complète passe sur 342 fichiers Lean et 27 584 constantes, avec aucune
exception pour une déclaration écrite, 572 audits explicites de contrôle sans
axiome et 23 fixtures d'échecs attendus. Les 31 contrôles d'intégration exigent
les sept indices payés et conservent leurs critères de livraison, d'origine,
de refus et de progression. Les quatre histoires du bootstrap et les 1 192
mutations textuelles des gardes passent également.
La [qualification](controle-metadonnees-tete-verification.json) enregistre les
410 sources et scripts figés avant la gate, inchangés jusqu'à sa sortie.

La liste des douze lectures de tête est traitée. D2 reste ouvert pour les
autres indices exécutables, l'ouverture et la normalisation documentaires,
les lecteurs différés, les frames et codecs, ainsi que l'administration et
les allocations complètes. Les enveloppes et réserves de D3, puis le secours
borné de D4 sur le présent conservé et rechargé, restent à implémenter.
A conserve sa priorité sur B.

## Ouverture contrôlée de la frontière

Le [raccord d'ouverture](controle-ouverture-frontiere.fr.md) remplace l'appel
natif à `VariableMaster.openFrontier` dans la recherche étendue par le parcours
de la frontière reçue, la vérification de fraîcheur, les résidus et leurs
témoins positifs `CnfWeakening`, la formation des enfants et les transports de
préservation. Il conserve l'ouverture et le `Master.Stage` originaux entiers.
Le splitter est indexé par les deux enfants réellement produits avant
l'expansion : les deux reconstructions cachées d'enfants révélées pendant la
relecture du C sont supprimées.

La borne locale est fermée pour toute formule, variable sélectionnée et
frontière de contextes engendrés reçues. Elle dépend de leur syntaxe sans
exécuter le moteur natif. Le paiement et le majorant de son propre bootstrap
restent à construire ; ce raccord ne ferme pas les enveloppes globales de D3.
Les fonctions de transport sont formées et conservées ; le coût de leurs
invocations différées demeure une obligation distincte.

La vérification complète réussit sur 344 fichiers Lean et 27 719 constantes,
sans exception pour une déclaration écrite. Les 613 audits explicites de
contrôle sont sans axiome. Les onze contrôles du composant, les 31 contrôles
d'intégration, les quatre histoires de génération et les 2 269 mutations
textuelles des gardes passent. La
[qualification](controle-ouverture-frontiere-verification.json) conserve les
413 empreintes figées avant cette vérification ; les résultats précédents
restent historiques.

D2 reste ouvert pour la normalisation, le routage et les invocations différées,
les autres indices exécutables, les frames et codecs, le bootstrap et
l'administration, les traces et les allocations complètes. D3 et D4 restent
à fermer suivant l'ordre du plan. A conserve sa priorité sur B.

## Normalisation contrôlée de la frontière

Le [raccord de normalisation](controle-normalisation-frontiere.fr.md) ouvre
les transformations et comparaisons de formules et d’histoires, la recherche
dans les deux directions, la classification, l’insertion et la normalisation.
Il construit le paquet `AcceptedIrreducibleFrontierReduction` original entier :
frontière retenue, code de routage, témoins dirigés et irréductibilité relative
au finder. Chaque constructeur de routage possède sa formation payée.
`expandedSearchCode` transmet cette réduction effectivement produite au même
`Master.Stage`, après la même ouverture et les mêmes contrôles de sources.

La borne locale est démontrée pour toute frontière de contextes engendrés
reçue. Elle est calculée depuis la syntaxe et la longueur de la source,
indépendamment du verdict de recherche et de la normalisation native. Les
preuves de provenance et de longueur majorent les insertions sur les sorties
réelles. Le paiement et le majorant indépendant du bootstrap de cette borne
restent à établir.

La gate complète réussit sur 347 fichiers Lean, 346 modules et 27 930
constantes, avec aucune exception pour une déclaration écrite. Les 680 audits
explicites de contrôle sont sans axiome, dont 67 nouveaux noms. Les dix-neuf
contrôles de normalisation, les 31 contrôles d’intégration, les contrôles
d’ouverture et de génération ainsi que les 23 fixtures d’échec attendu passent.
Les gardes rejettent 1 735 mutations textuelles de normalisation et 2 279
mutations de la voie étendue. La
[qualification](controle-normalisation-frontiere-verification.json) conserve
les 418 empreintes figées avant la gate, sans réécrire les résultats historiques.

La formation du code de normalisation est traitée. D2 reste ouvert pour
l’évaluation de ce code en préservations, puis les invocations de ces transports
et de leurs affectations différées, les autres indices, les frames et codecs,
les bootstraps, l’administration, les traces et les allocations complètes.
Le prochain raccord passe par `ControlCompletion.decideCode` : évaluer le code
reçu, composer avec la préservation d’ouverture, appliquer le routage à la
continuation, puis lire l’affectation transformée dans `completeCode`.
Les enveloppes globales de D3 et le secours sur le présent effectivement
conservé et rechargé de D4 restent à fermer. A conserve sa priorité sur B.

## Évaluation contrôlée du routage conservé

Le [raccord suivant de D2](controle-evaluation-frontiere.fr.md) évalue le
`AcceptedFrontierCode` effectivement reçu en une préservation originale entière,
avec ses transports avant et arrière et leurs lois d'acceptation. Chaque
constructeur est ouvert ; les compositions utilisent les vrais sous-paquets.
La préservation du même Stage compose ce résultat avec la préservation de son
ouverture réelle. Le nouveau `expandedDecideCode` consomme ce paquet et sa
continuation transportée dans la voie étendue du maître. La `Decision` et le
`Dossier.Step` originaux entiers sont conservés.

La borne locale est fermée pour tout code reçu de l'action SAT originale :
identité/échange 5, absorption 8, préfixage enfant +5, composition somme +5.
Le Stage ajoute 4. La décision possède la borne uniforme
`(ControlStagePreservation.bound stage + pairBound left right) + 3`, calculée
sans verdict de seed ni évaluation native. Les APIs et bornes historiques de
la décision et du maître restent intactes. Le calcul payé et le majorant
indépendant de leurs bootstraps restent à établir.

La gate complète passe sur 349 fichiers Lean, 348 modules et 27 996 constantes,
avec aucune exception pour une déclaration écrite. Les 703 audits explicites
de contrôle sont sans axiome, dont 23 nouvelles déclarations. Les treize
contrôles du composant, les 31 contrôles d'intégration et les 23 fixtures d'échec
attendu passent ; les contrôles de normalisation, d'ouverture et de génération
passent aussi. La garde nouvelle rejette 2 293 mutations textuelles. La
[qualification](controle-evaluation-frontiere-verification.json) conserve les
423 empreintes figées avant cette gate et les journaux de développement,
sans réécrire les qualifications historiques.

La formation des préservations et son raccord à la décision sont traités.
La prochaine obligation de D2 est l'application contrôlée de ces transports
à la continuation effectivement reçue, puis les requêtes de l'affectation
transformée. `citationRouting` et `citationAssignment` restent ouverts pour
leur coût interne. Les autres indices, les frames et codecs, les bootstraps,
l'administration, les traces et les allocations complètes restent également
à fermer, avant les enveloppes et réserves de D3 et le secours borné de D4 sur
le présent effectivement conservé et rechargé. A conserve sa priorité sur B.

## Applications contrôlées des transports et des affectations

Le [raccord suivant de D2](controle-application-transports.fr.md) ouvre les
invocations avant et arrière des transports, ainsi que les requêtes des
affectations qu'ils retournent. Les six constructeurs du routage SAT original
possèdent leurs exécutants et leurs bornes locales. La composition consomme
les vrais sous-paquets dans l'ordre de chaque direction ; le retour d'une
absorption conserve l'inclusion originale. Le lecteur retourné transporte
l'histoire de ses flips, sans identifier les occurrences sources.

Le maître produit une seule ouverture et une seule normalisation, conserve
leurs paquets entiers, puis évalue le code réellement retenu et compose ses
exécutants. `expandedRunCode` consomme le Stage et ce payload effectifs. La
décision obtient le Seed original avec son lecteur payé, applique le transport
avant puis interroge le lecteur reçu dans la complétion. Les égalités portent
sur la `Decision` et le `Dossier.Step` originaux entiers. Sur refus, la formation
du routage a lieu, mais aucune application de transport ou requête de lecteur
n'est exécutée. Les primitives opaques `citationRouting` et
`citationAssignment` disparaissent de cette voie effective.

Les bornes d'application et de requête sont démontrées sans exécuter les maps
natives pour trouver leur budget. Le lecteur générique est une hypothèse
positive reçue avec l'affectation ; les quatre Seed concrets ferment cette
hypothèse dans le maître. Les requêtes constantes coûtent 1, les requêtes d'un
flip sont majorées par `R.queryBound q + q + 3`, et les plafonds de lecteurs
sont propagés dans l'ordre réel des compositions. Leur propre calcul payé
et son bootstrap restent à établir.

La gate complète passe sur 358 fichiers Lean, 357 modules et 28 376
constantes, sans exception pour une déclaration écrite. Les 802 audits
explicites de contrôle, dont 99 nouveaux noms, sont sans axiome. Les 56
requêtes et six observations de lecteurs formés, les 23 contrôles
d'application avec 34 paires avant/arrière, les 31 contrôles d'intégration
et les 23 fixtures d'échec attendu passent. Les deux nouvelles gardes
rejettent 137 et 8 426 mutations textuelles de leurs entrées. La
[qualification](controle-application-transports-verification.json) conserve
les 436 empreintes figées avant la gate et la supervision indépendante,
sans réécrire les résultats historiques ni le registre scientifique.

L'obligation locale d'application des transports et de lecture de leurs
affectations est traitée. Ce compte rendu qualifie cet incrément, pas la
fermeture de D2. La liste précédente mêlait la couverture des calculs de D2
au bootstrap et aux enveloppes calculables de D3. Le
[dossier de clôture de D2](cloture-d2.fr.md) fixe désormais les obligations
de couverture du lecteur effectivement transmis, des frames, des recettes,
de la composition, des traces et des allocations abstraites. Toute obligation
non classée ou non vérifiée maintient D2 ouvert.

D3 conserve le bootstrap payé, les enveloppes globales et les réserves de
successeur ; D4 doit raccorder le secours borné au présent réellement conservé
et rechargé. Les codecs et l'activation relèvent aussi d'A1.
`RecoveryData.prepare` utilise encore `Memory.step` nativement. La réalisation
en cours transmet le lecteur au maître et à ses frames. L'exécuteur final
conserve les événements intrinsèques des compositions ; ses lois CTL, son
unicité et son arrêt faute de carburant sont prouvés sur le résultat entier.
Les projections causales reprennent maintenant l'histoire et la génération
reçues, et la décomposition transmet sa racine mesurée à la continuation et
à la frame suivante. Leur qualification finale reste à effectuer.
La revue du consommateur complet a détecté une réinstrumentation exponentielle
des événements administratifs par `Code.bind`. `bindForward` conserve désormais
les événements reçus et le runner prépaie leurs couches effectives ; les lois
générales et 140 attentes indépendantes qualifient localement cette correction.
La formation générique de frame et l'amorçage du maître paient également leur
lecture de source. Les premières sondes terminales ont rencontré des plafonds
de fixture puis une limite de pile hôte ; un prototype à frames denses a
ensuite conservé trop de closures administratives. Ces échecs restent archivés.

Le consommateur public utilise maintenant `ControlCompactExecution`. Il
retourne une trace positive `Path` et la tape administrative, avec la valeur
constitutive entière. Ses lois générales et son raffinement constructif
conservent les coûts, les budgets, les arrêts et le résultat original. La
première citation réelle termine et son lecteur reçu passe les requêtes ; les
140 coupons indépendants passent aussi avec cet exécuteur. Le catalogue donne
3 016 666 780 unités terminales pour cette première citation. C'est le coût
d'une fixture de validation, pas une enveloppe calculable de production.

La revue compilée a figé 1 887 corps, 40 frontières de fonctions originales
stockées et les sites des 35 symboles FFI. Les gardes rejettent 1 977 mutations
pour cet inventaire et 152 pour le consommateur compact. Les scénarios publics
conservent toutes les branches, valeurs, origines, lecteurs et justifications
des fixtures précédentes ; ils exécutent chaque grosse étape une seule fois.
Les tests des budgets restent indépendants, avec les 140 coupons et une
citation réelle à coût figé. Les scénarios publics passent en développement,
mais la troisième gate confirmatoire échoue sur le délai physique du client
étendu, avec les 485 entrées figées et les 30 anciens reçus inchangés. La
reprise native v2 a généré 241 modules avec C identique au C revu, puis échoué
sur un champ obligatoire absent de la configuration du client, avant tout
audit ou assertion de ce client. La reprise v4 corrigée est lancée après
revue indépendante ; le contrôle officiel de la configuration et les 17 audits
du même client, les 242 compilations d'objets et la liaison passent. Le parcours
natif des cas est effectivement lancé, puis le client et son lanceur sont
constatés absents à 21 h 19 sans reçu de fin ni sortie. L'arrêt et le redémarrage
du service sandbox Codex à 21 h 18 sont établis par les événements Windows,
sans preuve directe de la cause de disparition du client. Aucun code de sortie,
dépassement de délai ni verdict sur ses 31 assertions n'est revendiqué.
La revue racine recontrôle 14 974 empreintes sans différence et conserve cette
tentative sans relance. Les cas, carburants et attentes
restent identiques. Le dossier détaille les coûts de
composition et de traces identifiés, ainsi que les mesures qui restent à
effectuer. Une sonde indépendante du `Code.bind` original confirme désormais
les `2n` événements et `n(n−1)` couches de la famille identité : pour 512,
1 024 et 2 048 compositions, les temps observés sont 2,6713, 11,1001 et
43,0762 ms. Ses huit audits sont sans axiome, ses sorties brutes et
14 975 empreintes sont recontrôlées. Le dossier précise le périmètre de
mesure. La capture suivante du vrai client couvre aussi le nouveau thread
de calcul : 1 550 de ses 1 577 piles contiennent le callback de `bindForward`.
La revue racine contrôle 17 113 échantillons, 213 644 adresses et 14 979
empreintes inchangées. Ce sont des présences de fonctions dans une fenêtre
de 60 secondes, sans pourcentage exact du CPU ni verdict sur les 31 assertions.
La lecture indépendante du C distingue aussi huit `SourceResult` mis en
cellules globales et trois initialisateurs scalaires ; le runtime once reçu
rend les premiers persistants. Le dossier conserve les reçus et les limites
de ces constats. Une génération externe du client exact avec l'option
`compiler.extract_closed=false` supprime les huit cellules dans le C ;
les 17 audits restent sans axiome et 14 989 empreintes sont recontrôlées.
Aucun objet ni runtime de ce candidat n'est revendiqué. La correction des
callbacks dispose maintenant d'un premier incrément sémantique qualifié :
recettes et pile de continuations typées, avec équations sur le `Code` entier.
La compilation v2 rejetée est conservée ; la correction v3 garde les mêmes
énoncés et termine avec exactement 24 audits sans axiome. La revue racine
contrôle les sorties brutes, les corps C d'entrée de composition et de retour,
15 004 empreintes inchangées, puis les 485 entrées et les 30 anciens reçus.
Ces deux fonctions locales conservent la continuation reçue et son résultat,
sans appeler les dénotations denses. L'exécuteur complet, ses traces, ses
coûts et sa fermeture générale restent à établir. Un second incrément conserve
la profondeur dans les frames avec un accord général prouvé ; ses 16 audits
sans axiome et 15 015 empreintes inchangées sont vérifiés indépendamment.
Les helpers compilés ne parcourent pas la pile ; le prochain appelant doit
lire les champs de la frame reçue et prépayer les calculs entiers, les appels
et les constructions effectives. Les événements source conservés restent
distincts des opérations terminales réellement exécutées.
Un troisième incrément établit les blocs ordonnés de l'événement métier avec
17 audits sans axiome ; sa revue indépendante contrôle les bruts, le C et
15 022 empreintes inchangées. Sa grammaire positive n'est pas encore une trace
produite par une course. La carte de migration relue suit tous les producteurs,
les interfaces différées et les successeurs jusqu'à l'entrée publique, avec
les cinq critères conservés. L'agent prépare l'opérateur payé qui devra lire
les vraies frames, puis le modèle de course et le raccord des traces.
L'ensemble attend une nouvelle gate complète.
**D2 reste ouvert** : une réussite locale ne remplace pas la gate
complète et sa revue. D3, D4 et A1 conservent leurs obligations, et A précède B.

La relecture suivante retrouve deux descentes anticipées dans la formation
des lecteurs mesurés : `recipeCode` construit récursivement son code avant
les paiements de cellules, et `visitCode` invoque le lecteur précédent avant
sa propre transition. Leur correction minimale est préparée sous supervision,
avec conservation des résultats originaux et contrôle de l'ordre dans le C.
Les sources restent figées pendant le parcours natif du client étendu inchangé,
dont le nouvel objet et le lien ont réussi. Cette exécution et les corrections
devront ensuite être qualifiées par un nouveau protocole de gate complète.
Les prototypes externes de nouvelle composition ne deviennent pas, par leur
seule existence, une condition supplémentaire de clôture de D2.

La revue des transports détecte en outre une application réelle des closures
de plafond dans `transForward` et `transBackward`. Leur récursion ne peut être
classée comme un index effacé : le C invoque la borne du premier enfant avant
l'application du second. Le raccord préparé conserve le plafond effectivement
produit et le transmet au consommateur, avec réalisation payée des
transformateurs nécessaires. Les fonctions de bornes utilisées uniquement dans
les preuves restent séparées. Ce défaut de couverture doit être réparé dans
D2 ; il ne déplace pas les obligations globales de bootstrap de D3.

La correction locale du lecteur est maintenant vérifiée effectivement. Le
protocole externe de préfixes v5 conserve les 24 cas et les deux séries de
sept contrôles, les mêmes attentes et le même délai de 600 secondes. Le
lanceur place les options de compilation et de setup avant le fichier de
--run : après celui-ci, Lean les transmet au programme et n'utilise pas
l'artefact corrigé. Le diagnostic v3 observe les deux ordres de commande avec
un audit propre et les arguments réellement reçus.

La course v5 termine avec sortie zéro en 3,9551292 secondes, exactement huit
audits sans axiome, le marqueur attendu et aucun flux d'erreur. La revue racine
recontrôle 15 540 entrées du protocole, 15 542 premières empreintes du résultat
et l'environnement, sans différence. Son reçu autonome externe est
measured-reader-payment-prefix-v5-root-actual-review-v1.json, SHA-256
4ec09767209888a8daff30c2663d9d28fe8b252c376d270011b9f80c16326801.
Tous les essais rejetés restent conservés. Cette réussite qualifie seulement
les contrôles locaux du lecteur ; le raccord des plafonds aux consommateurs
concrets et la nouvelle gate complète restent exigés pour fermer D2.

Les 104 régressions prescrites des lecteurs passent désormais sur les artefacts
corrigés : 72 cas du lecteur mesuré et 32 cas de transport. Les bits, nombres
de nœuds et étapes historiques restent identiques ; les attentes de traces
comptent les transitions supplémentaires réellement payées. Les phases
terminent avec sortie zéro en 270,3184684 et 167,4125794 secondes, dans les
mêmes délais de 300 secondes, avec six puis quinze audits sans axiome et les
deux marqueurs exacts. Le transport a été recompilé avec le nouveau lecteur :
une première préparation utilisant ses anciennes closures inlinées a été
rejetée avant exécution et conservée.

Le reçu racine reader-regression-payment-v4-root-actual-review-v1.json,
SHA-256 7f79222ce841a27156f67cf51df745938d2da6302052b7ffaaedbe767563297f,
recontrôle 15 574 premières empreintes pour chaque phase, l'environnement et
les flux bruts. La revue indépendante v10 confirme ces résultats, avec
SHA-256 66d759e22444e85ec7cc46bed5ab760498c6e2b13cd742744d8cb9c6fa3bd755.
Le composite corrigé transmet aussi le plafond Nat effectivement retourné
par le premier enfant au second, avec les mêmes continuation et lecteur.
Ses douze audits et le C entier sont relus ; les closures de métadonnées
historiques restent conservées dans le paquet original entier, sans être
invoquées dans ce nouveau chemin d'application. Ce raccord local et les
régressions ne remplacent pas la qualification des consommateurs publics ni
la gate complète exigées pour fermer D2.

## Adoption des corrections de couverture et de consommation

Les treize sources qualifiées ont été adoptées octet exact. Les dix fichiers du
raccord des plafonds et du maître totalisent 95 audits, le lecteur mesuré 18,
et les deux modules compacts 53 : 166 noms au total. Les 104 régressions du
lecteur et des transports et les 80 coupons indépendants de plafond ont
effectivement réussi. Ces résultats sont conservés séparément de la
qualification des consommateurs publics reconstruits et de la gate complète.

Le transformateur payé conserve le Nat réellement retourné. La composition
transmet au second enfant la continuation, le lecteur et ce plafond du premier
enfant, dans l'ordre de la direction. L'évaluation de la route paie sa cellule
avant de sélectionner le constructeur et de descendre. Le Stage conserve
l'original entier de la composition effectivement produite ; la complétion
utilise sa vraie application. Les fonctions historiques de métadonnées restent
dans leurs paquets originaux, sans invocation sur cette nouvelle voie.

La consommation de la pile compacte libère chaque cellule terminée avant de
poursuivre sur sa queue. Le helper monomorphe transfère seulement le pointeur
reçu. Sur la voie terminale payée, son invocation suit un returnPaid réussi ;
un échec de paiement retourne sans ce helper. Un arrêt métier peut toutefois
remonter avec le suffixe d'échec, sa formation de frame ayant déjà été payée à
l'entrée. Cette opération ABI fixe appartient à la primitive de frame déclarée ;
elle ne constitue ni un parcours gratuit de la queue ni une borne physique.

Le protocole externe d'adoption
adopt-qualified-d2-sources-root-v1-protocol.json porte le SHA-256
a0e01006edc1eff541a0e55c46d8ca9e44edc7dec5bb089df1a1e3846393a16f.
Les 485 sources, scripts et configurations antérieurs et les trente reçus
historiques ont été archivés octet exact avant la mutation. Les nouvelles
gardes de paiement du lecteur et de consommation compacte rejettent
respectivement 32 et 17 mutations textuelles, en complément des anciens
contrôles conservés. Leurs préparations rejetées sont également conservées.

Le client natif historique est constaté absent, avec son lanceur, après le
changement de runtime du poste ; aucun reçu de fin n'a été reçu. Les 15 483
premières empreintes de fichiers restent disponibles et identiques, et seul
PATH a changé dans l'environnement. Le reçu externe
native-expanded-no-extract-v4-inconclusive-current-runtime-root-v1.json,
SHA-256 d269fecd20b65b00be36a30a284e747e307ec979f041da201ee0a1b86a5778b5,
ne lui attribue ni code de sortie, ni dépassement de délai, ni verdict
d'assertions. Cette tentative reste distincte de la correction du Trail.

La reconstruction publique courante et la revue des C entiers ont maintenant
terminé : 26 modules concernés, 333 audits sans axiome, et comparaison exacte
des 14 C modifiés après les seules substitutions explicites du namespace.
Les générations externes du client historique et du client public sont
également reçues et revues, avec respectivement 4 896 + 17 et 5 094 + 31 audits
sans axiome. L'inventaire courant suit 1 994 corps, dont 52 fonctions originales
stockées ; sa garde réelle rejette 2 060 mutations sans modifier ses sept
racines ni les contrats reçus.

Les 242 objets historiques et leur lien passent. Le même client termine
ensuite avec sortie 1 après 6 407,736 secondes, sans dépassement du délai :
son flux d'erreur signale un manque de mémoire. Aucun verdict des 31 conditions
n'est reçu. Les premières empreintes et les artefacts natifs restent identiques.
La prochaine correction doit partir d'une localisation explicite de cette
croissance mémoire ; elle conserve les cas, carburants et attentes prescrits.
Le client public des cinq étapes reste préparé et relu, sans nouveau runtime.
Le coût historique de citation doit aussi être requalifié sur les nouveaux
paiements avant les variantes de budget. Ces contrôles restent distincts de
la suite complète finale. D2 demeure ouvert jusqu'au reçu autonome et à la
revue des cinq critères du dossier. D3, D4 et A1 conservent leurs obligations ;
A précède B.


Le diagnostic court reçu localise le parcours avant le retour de la première
citation de loadedOk, depuis le présent effectivement rechargé. Les imports
et six initialisations se terminent ; les variantes exactes, courtes et
excédentaires de cette citation ne commencent pas. Leur rétention entre
parcours ne peut donc expliquer la croissance précédant ce premier retour.
L'obligation immédiate consiste à localiser et corriger le calcul intérieur,
en conservant tous les cas, carburants et observations exigés, puis à reprendre
la qualification complète sur les sources finales figées. La revue racine du
diagnostic porte le SHA-256
43979d25a4ff404e2ddb386c4a22bed638bb267af65ef1f57e7ba1cbee96d1d8.
Cette localisation maintient D2 ouvert ; D3, D4 et A1 restent distincts.

Le diagnostic interne a maintenant localisé l'accumulation avant la
restauration du premier calcul de loadedOk : sa dernière publication
complète porte 71 237 632 transitions, dont 71 086 978 administratives.
Une correction externe de l'addition utilise une pile positive payée en
conservant les valeurs et les labels métier pour tout carburant. Le maximum
est préparé pour ses usages ultérieurs. La revue source est faite ; Lean,
le C, l'intégration, les mêmes régressions et la gate finale doivent encore
qualifier cette correction. Le
[dossier de D2](cloture-d2.fr.md) conserve les preuves de réception et leurs
limites ; D2 reste ouvert.

Le correctif arithmétique a maintenant passé le contrôle Lean/C strict :
39 audits sans axiome pour le candidat, puis 113 audits pour chacun des
passages frontend et génération de sa chaîne externe de six modules.
Le graphe C des 14 producteurs et callbacks conserve le paiement, la vraie
pile et sa consommation ; les accords historiques portent sur toutes les
entrées et tous les carburants. L'administration décrit le travail nouveau
réel. Les autres consommateurs, les mêmes régressions et la gate finale
restent à qualifier avant adoption et clôture ; le
[dossier de D2](cloture-d2.fr.md) conserve les reçus et les tentatives rejetées.

La reconstruction externe de tous les consommateurs affectés est maintenant
reçue : 76 modules, 152 premières sorties et 152 phases admises avec sortie 0.
Le contrôle exhaustif reçoit 30 357 constantes, 364 exceptions générées
classifiées et zéro exception écrite ; les noms audités sont sans axiome.
Le reçu racine contrôle les entrées, les imports frais, les sorties et les
trente reçus historiques sans différence. Les tentatives au délai et les
préparations non exécutées restent conservées séparément. Le
[dossier de D2](cloture-d2.fr.md) expose cette réception. Les gardes textuels,
la revue de leur inventaire, les mêmes régressions, l'adoption et la gate
finale restent à qualifier ; ce résultat de génération ne clôt pas D2.


Les gardes arithmétiques ont maintenant terminé leur qualification textuelle
sur les C externes reçus : deux références acceptées et 589 mutations rejetées,
avec les 91 anciens cas conservés. Le reçu racine contrôle les résultats et
les premières empreintes sans différence. Le relevé du graphe expose
12 ajouts, 14 retraits et 39 corps modifiés ; il ne met pas à jour l'inventaire
avant la revue des corps et de leurs interfaces. Les mêmes régressions métier,
l'adoption et la gate complète finale restent nécessaires. Le
[dossier de D2](cloture-d2.fr.md) conserve cette étape de qualification ;
D2 demeure ouvert.


La régression native des 31 conditions passe désormais après la correction
arithmétique : 242 objets nouveaux, lien et runtime ont tous terminé avec
sortie 0. Le runtime dure 25,662 secondes, rend le marqueur exact et garde
un flux d'erreur vide. Les mêmes cas, attentes et carburants sont conservés ;
la revue racine et la revue indépendante contrôlent les phases, les premières
empreintes et les trente reçus historiques sans différence. Le
[dossier de D2](cloture-d2.fr.md) distingue cette réussite effective de l'ancien
échec mémoire conservé. Les contrôles publics, le prix courant, l'adoption
et la gate finale restent exigés avant la clôture.

### Consommateurs publics et prix courant qualifiés — 12 octobre 2026

Le contrôle du graphe accepte la base puis rejette les 2 058 mutations
originales. Le scénario public des cinq étapes réussit en exécution native,
avec ses sept vérifications de branches et douze fixtures de requêtes.
L'observation indépendante de la citation courante réussit également :
son prix de catalogue est 45 988 723, figé avant les tests exact, moins un,
nul et plus 17 ; la valeur, les origines, la restauration, le lecteur et
le chemin positif demeurent vérifiés. Le dossier de clôture conserve les
reçus autonomes et leurs revues indépendantes.

La correction arithmétique et l'inventaire restent externes à ce stade.
Les tests aux budgets figés, leur adoption et la gate complète finale sont
les passages restants de D2. D2 n'est pas encore fermé ; D3, D4 et A1 restent
leurs obligations propres et A conserve sa priorité sur B.

### Qualification complète de D2 sur l'arbre intégré — 12 octobre 2026

Les douze fichiers qualifiés sont adoptés et le correctif EOF de deux octets
est reçu séparément. G1 demeure une tentative rejetée au contrôle final de
diff ; G2 est une nouvelle exécution complète sur un nouveau gel. Elle termine
avec sortie 0, ses 392 fichiers Lean vérifiés, les audits, l'inventaire fermé,
les contrôles de partage et les 23 cas d'échec attendu.

Les trois nouveaux clients natifs réussissent : 31 conditions historiques,
cinq étapes publiques et leurs branches, puis les quatre budgets fixés avant
l'expérience à partir du prix indépendant 45 988 723. Les productions entières,
lecteurs et successeurs sont consommés par leurs vrais chemins. Les premières
empreintes, l'environnement, les ensembles de sources et les 30 anciens reçus
sont contrôlés sans différence. La réception racine et la revue indépendante
confrontent ces résultats aux cinq critères du dossier, sous les hypothèses
explicites des preuves générales.

Le [reçu autonome de D2](cloture-d2-verification.json) et le
[dossier de clôture](cloture-d2.fr.md) font foi pour ce snapshot qualifié.
Les vérifications documentaires, les liens et le diff passent ; D2 est clos.
Le registre scientifique et les reçus historiques conservent leurs statuts
et leurs empreintes antérieurs.

La prochaine obligation est D3 : calculer les enveloppes du contrôle et de
son bootstrap avant l'appel, protéger la réserve obligatoire de l'activité
facultative et établir leur fermeture dans les successeurs. D4 compose ensuite
les tours et le secours dans cette allocation, avec le paquet réel, le progrès
et la fermeture. A1 établit le chargement de toutes les ressources maître et
du présent, sa couverture positive, ses octets, son activation et sa reprise
utilisable. Les phases et transactions restent A2 ; les opérations physiques
A3 ; le raccord Qwen et la comparaison A4/A5. A garde sa priorité sur B.
