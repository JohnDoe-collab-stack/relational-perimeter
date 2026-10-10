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
de la formation, du maître et des assemblages reste la prochaine frontière.
