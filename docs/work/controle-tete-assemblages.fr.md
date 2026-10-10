# Ouverture de la tête et des autres obligations de D2

Cet incrément implémente des passages dans les deux volets demandés sur
`codex/align-persist-recovery`, depuis
`130392f031c165dd57895262bf79209af240b85e` : les productions internes de
`masterHead` et les autres obligations du
[plan d'application](application-alignement-persistant.fr.md).
La [spécification v0.3](RP_ALIGN_PERSIST_SPEC_v0_3.fr.md) reste la cible.
**La demande entière et D2 ne sont pas encore terminés.** Les résultats
ci-dessous qualifient les passages construits ; la liste des ouvertures
restantes fait partie du résultat de la vérification.

## La même tête et le même successeur

[Le contrôle de tête](../../Tests/LocalAlignment/DocumentaryControlMasterHead.lean)
exécute les quatre productions `discover`, `applyStage`, `decompose` et
`assemble`, puis les trois productions de continuation : préfixe, source et
fraîcheur. Les arguments sont lus dans le support effectivement constitué.
Chaque formation stocke le producteur original et la formation antérieure.
Les opérations suivantes consomment les données réellement retournées.

La preuve porte sur `VariableMaster.MasterHead` entier : tête, curseur suivant
et raccord de frontière. Les égalités servent à aligner les types dépendants.
Les constructeurs privés sont employés par le mécanisme ordinaire de
construction de Lean, avec leurs obligations fermées ; aucun accès à un nom
privé généré ni mécanisme de remplacement de preuve n'est ajouté.

[La génération](../../Tests/LocalAlignment/DocumentaryControlMasterGeneration.lean)
ouvre la construction récursive de la clause de leurres, les assemblages de
formule, la racine et l'extraction. Celle-ci reçoit cette racine, garde l'ordre
et les doublons des candidats, et paie les concaténations et additions de ses
compteurs. Les compteurs retournés sont ceux de la même extraction.

[Le filtrage de provenance](../../Tests/LocalAlignment/DocumentaryControlProvenance.lean)
paie chaque cellule, les comparaisons naturelles exécutées, la liste conservée,
les rejets, la trace et les additions de visites. Il conserve le résultat
entier du filtre original, pas seulement les candidats retenus.

[Le parcours des candidats](../../Tests/LocalAlignment/DocumentaryControlMasterCandidates.lean)
ouvre les tailles de représentation du calcul de `candidateAttemptWork`,
les cellules du parcours et l'assemblage de tous ses compteurs. Le premier
succès arrête ce parcours ; un échec consomme la suite effective. Le paquet
conserve les endpoints produits, le préfixe essayé, les tentatives et les
travaux de comparaison et de construction.
[La tentative](../../Tests/LocalAlignment/DocumentaryControlMeasuredDiscovery.lean)
ouvre maintenant aussi les comparaisons structurelles et unaires, la
fraîcheur, les résidus, les deux enfants effectivement constitués, les
transformations de formule et d'histoire et la recherche de relation.
Les échecs court-circuitent les lectures suivantes comme dans l'original.
Le résultat conserve `MeasuredCandidateRun` entier et ses endpoints en
`Type`. Le code contrôlé n'appelle plus `tryMeasuredCandidate` pour le produire.

[L'application](../../Tests/LocalAlignment/DocumentaryControlMasterApplication.lean)
consomme ce résultat sans rappeler le constructeur natif entier.
[Le schedule stocké](../../Tests/LocalAlignment/DocumentaryControlMeasuredSchedule.lean)
lit les endpoints conservés. Ses deux recherches restent distinctes, comme
dans l'original, et passent par le chercheur de relation contrôlé. Les paquets
de validation, d'exécution, de closure et d'état produit sont assemblés depuis
leurs résultats effectifs.
[Le transport](../../Tests/LocalAlignment/DocumentaryControlMeasuredTransport.lean)
interprète les branches identité, atome et composition. La seconde composante
consomme la sortie de la première ; les deux additions de compteurs sont
contrôlées. Le paquet `AppliedDiscoveryExecution` conserve cette sortie.
[Le stade](../../Tests/LocalAlignment/DocumentaryControlSequentialStage.lean)
reçoit ces paquets, la continuation d'entrée et l'assignation suivante.
Sa preuve d'accord porte sur `SequentialStageRun` entier.

[Le successeur](../../Tests/LocalAlignment/DocumentaryControlNextState.lean)
paie la formation de provenance, la lecture de la seed dans l'état exécuté,
la requête du bit effectif et l'assemblage de l'état suivant. Il conserve
`NextOperationalStateRun` entier et reçoit le target antérieurement produit.
Le moteur de génération constitutive et l'intérieur de la fonction interrogée
restent des frontières nommées. Une transition nommée à leur entrée ne ferme
pas leur coût interne.

[La décomposition](../../Tests/LocalAlignment/DocumentaryControlMasterDecomposition.lean)
forme séparément les deux occurrences et leurs témoins positifs de
constitution, puis conserve la licence entière. Elle exécute les sorties
transformée et retenue sur ces identités.
[L'image contrôlée](../../Tests/LocalAlignment/DocumentaryControlProducedImage.lean)
parcourt la frontier source réelle, conserve chaque sortie, puis exécute
la déduplication sur la liste ainsi produite. Son ordre conserve la dernière
occurrence, conformément à l'original. Le régime entier, dont la fonction
`carry`, est conservé. Cette fonction conserve ses appels différés
originaux ; leur lecture contrôlée reste à raccorder. Aucun singleton ne
remplace la construction de l'image. L'ouverture du rôle et l'intérieur des
formations d'occurrences restent à ouvrir.

## Assemblages, restauration et administration

[L'assemblage de citation](../../Tests/LocalAlignment/DocumentaryControlQuotationAssembly.lean)
forme la ressource d'incorporation depuis le paquet autorisé réel. Il paie
ensuite connaissance, kind, liste de kinds, stockage, extension, occurrence,
dossier, frame et paquet. La connaissance reçoit le support payé, avec sa
formation. L'égalité porte sur l'étape originale entière, y compris son
transport et son témoin de progression en `Type`.

[L'entrée manquante](../../Tests/LocalAlignment/DocumentaryControlMissingAssembly.lean)
a cinq constructions payées : entrée dans l'assemblage, extension identité,
sortie absente, frame et paquet. Elle conserve le même échec et la même
fonction de progression impossible. La borne générique de cet assemblage
est prouvée égale à cinq transitions.

[Les lectures différées](../../Tests/LocalAlignment/DocumentaryControlDeferred.lean)
comprennent la restauration de frame et les lectures de sa table finie.
L'interface de lecture des justifications distingue explicitement une
fonction reçue d'un lecteur contrôlé. Les lecteurs vide, citation et déduction
sont fermés constructivement. La déduction lit les deux justifications et
paie leurs positions avant de former l'arbre réel, avec la permission et
l'action de formation reçues. `KnowledgeRecipe` représente ces constructions
et ferme la terminaison de leurs lecteurs, sans hypothèse de lecteur antérieur
non réalisée. `ExtensionRecipe` représente les transports identité, ajout
et composition, avec lectures payées de leurs recettes. Leur raccord à toutes
les frames et à leurs codecs reste à construire.

[L'administration](../../Tests/LocalAlignment/DocumentaryControlAdministration.lean)
contient une composition payée et un évaluateur du programme source qui
paie inspection, appel, frame, construction de liste de trace, témoin `Eval`
et paquet de résultat. Il est prouvé égal au résultat entier de
`Control.execute` et possède une preuve constructive de terminaison pour
chaque carburant source fixé. Le C vérifie qu'il n'appelle pas cet évaluateur
source natif pour fabriquer son résultat.

Cette administration modélise les constructions abstraites de l'évaluateur
source. Elle ne couvre pas l'exécution du runner hôte ni les appels à
`Code.bind` cachés dans les callbacks des programmes historiques. Elle ne
constitue pas une borne de heap physique ni une réservation de mémoire.

## Raccord exécuté et limites

`ControlMaster.expandedSearchCode` et `expandedRunCode` raccordent la tête
contrôlée à la recherche documentaire.
`ControlStep.expandedCode` ajoute la restauration payée, les assemblages de
citation et d'entrée manquante, et conserve l'égalité avec `Program.step`.
Sa terminaison est prouvée ; le majorant de bootstrap de cette voie n'est pas
encore construit. Les API historiques et leurs relevés gardent leur portée
antérieure. `RecoveryData.prepare` appelle encore son étape native : la
substitution complète du secours et ses enveloppes sont des obligations
ultérieures, pas un effet de cet incrément.

| Obligation | Résultat courant | Travail encore requis |
| --- | --- | --- |
| Chaîne des sept productions de tête | Même paquet entier et mêmes formations, raccord expérimental exécuté | Coût des métadonnées dépendantes et fermeture des moteurs ci-dessous |
| Génération, extraction, provenance et tentatives | Boucles, listes, compteurs, transformations, comparaisons et endpoints instrumentés | Coûts des métadonnées du raccord maître |
| Application et décomposition | Schedules, deux recherches, transport composé, stade, successeur, licence et image construits depuis leurs productions ; accord entier | Générateur constitutif, ouverture du rôle, intérieur des formations et appels différés |
| Ouverture et normalisation | Productions réelles conservées dans la recherche | Recursions et moteurs relationnels internes |
| Préservation, routage et assignation | Raccords antérieurs conservés | Construction des maps, interprétation de leurs appels différés et lecteurs d'assignation |
| Citation et entrée manquante | Assemblages décomposés, égalité des étapes entières | Fermeture des lecteurs qu'elles retiennent pour tous les successeurs |
| Restauration et justification | Frame, table finie, lecteurs vide/citation/déduction et recettes de transports | Raccord exécuté de tous les lecteurs et de leurs représentations portables |
| Administration | Évaluateur source et composition payés, résultat entier conservé | Migration des callbacks historiques, enveloppes d'allocation et runner déclaré |

Le contrôle C trouve **douze sites directs de lectures natives de
métadonnées dans le contrôle de tête**. Ils comprennent les arguments des
producteurs et les lectures nécessaires aux kinds dépendants. Les garder
dans le champ de la revue évite de confondre une sortie payée fidèlement
conservée avec le comptage complet du code qui la prépare. Le contrôle ne
revendique donc pas l'absence de toute lecture native ni la fermeture du
graphe d'appels. Deux des quatre lectures natives de `DiscoverySchedule.entry`
apparues dans le nouveau raccord ont été supprimées : la variable est lue
directement dans la découverte effective. Deux sites restent nécessaires à
la représentation actuelle des indices exécutables d'endpoints. Leur fermeture
requiert la transmission des données mises en cache sous contrôle. L'accord
mathématique entier ne constitue pas une preuve que ces reconstructions ont
disparu du code compilé.

## Vérification locale

Les [cas Lean](../../Tests/LocalAlignment/DocumentaryExpandedControlCases.lean)
établissent les seuils 8 et 10 pour les deux entrées manquantes et 24 pour
le refus d'une règle, avec échec à une unité en moins. L'évaluateur source
instrumenté termine en quatre transitions pour `done` et en vingt-et-une
pour une transition source suivie de `done`, dans le catalogue déclaré.
Les mêmes codes sont conservés après reset et pour les deux histoires
oubliées de la fixture existante.

Une première version du
[smoke](../../scripts/run-documentary-expanded-control-smoke.py) a passé
26 vérifications de développement, avec douze audits runtime sans axiome :
citations et origines, tête unique, formations, reset, oubli, chargement de
composant, refus, entrées manquantes, administration, courts-circuits,
endpoints, échecs de relation, justification dérivée et composition des
transports. Son plafond de test
200 000 est annoncé ; ce plafond n'est pas une borne de bootstrap prouvée.
Les tests de seuil de citation utilisent la longueur de la trace obtenue,
comme contrôle des lois de l'interprète, et non comme attente indépendante
d'une borne annoncée. Le relevé intermédiaire de 23 104 transitions concernait
la version où l'intérieur de chaque tentative restait complexe ; les anciens
106 pas comptaient davantage de moteurs complexes. Ces relevés historiques
ne sont pas des mesures de performance de la version étendue finale.

Les transports identité, atome et composition ont des seuils indépendamment
annoncés et vérifiés par le noyau : respectivement 2, 5 et 18, avec expiration
à une unité en moins. La composition de deux atomes conserve les deux
applications et leur sortie effective. Les lectures de bits dans ces tests
sont des observations ; elles n'annoncent pas un coût interne fermé des
assignations. Le protocole runtime est étendu à 31 vérifications et seize
audits, comprenant ces trois cas, l'ordre de déduplication et le passage
stockage/validation/exécution d'un schedule sur endpoints réellement produits.

La qualification a conservé deux réparations de développement : un plafond
initial de 8 192 insuffisant, et une dépendance générée à `propext` dans le
client de test. La seconde provenait de l'optimisation des matchs clairsemés
et d'une représentation de diagnostic ; le client emploie les cas
constructifs et un diagnostic constant. Ses audits vérifient le résultat.
Ces runs sont des tests de développement, pas une expérience confirmatoire
dont le protocole aurait été changé après observation.

Les [gardes C](../../scripts/check-documentary-expanded-control-codegen.py)
rejettent 683 mutations textuelles dans le relevé ciblé de développement.
Elles vérifient les frontières nommées,
la conservation de la tête et du curseur réellement produits, les valeurs
de formation, les deux endpoints de la tentative, et l'absence des appels
directs aux comparateurs, transformations, tentatives et producteurs entiers
remplacés. Elles contrôlent aussi les champs effectifs du stade, du
successeur, des deux constitutions, de la licence et de la frontier image.
Leurs mutations testent le checker, pas l'exécution de mutants.

La gate complète `scripts/verify.ps1` a réussi sur l'arbre courant :
337 fichiers Lean, 336 modules audités, 27 371 constantes, aucune exception
pour une déclaration écrite et 23 fixtures d'échecs attendus avec leurs
diagnostics exacts. Les 39 modules de contrôle comportent 486 audits explicites
sans axiome. Cette même gate a passé les 31 contrôles runtime et leurs seize
audits, ainsi que les 683 mutations du contrôleur C. Les empreintes des
fichiers de code et de configuration sont identiques au snapshot capturé
avant ce run. Le contrôle documentaire est repris après la rédaction de ce
relevé ; aucun verdict d'audit indépendant ni évidence sur un commit figé
n'en découle.

Le [relevé de vérification](controle-tete-assemblages-verification.json)
consigne les empreintes et la gate de cette révision. Les qualifications
antérieures restent historiques. D2 entier, CONT-03 et P15 restent ouverts ;
D3 puis D4 suivent sa fermeture complète, et A conserve la priorité sur B.
