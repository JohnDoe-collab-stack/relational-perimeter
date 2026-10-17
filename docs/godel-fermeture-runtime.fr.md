# Fermeture runtime et distinction gödelienne sous un contrat exact

## Portée et statut

Pour un témoin diagonal effectivement produit, on fixe d'abord deux sources,
un contrat de futurs et une réalisation exacte de ce contrat. Les deux sources
portent le même témoin et des rôles différents : le rôle sémantique lit le type
de vérité de la phrase produite ; le rôle syntaxique lit son type de preuve.
La requête canonique de fermeture est exécutée séparément sur ces sources.
Le niveau opérationnel sans loi de readout possède une réalisation positive :
il oublie le rôle, préserve exactement autorisations, transitions et événements,
et produit une collision des deux sorties. Si cette même collision est demandée
sous exactitude du readout, elle impose `Truth(G) = Proof(G)`, puis la conversion
de la vérité en preuve du même énoncé. Cette conversion rencontre la
non-prouvabilité certifiée de ce même témoin.

La collision est une hypothèse de fermeture, non une conséquence de Gödel.
L'action est autorisée et exécutable indépendamment de cette hypothèse.
Le résultat quantifie sur toute réalisation exacte du contrat fixé ; il
n'affirme ni l'impossibilité de tout regroupement, ni celle de toute notion de
fermeture. Il ne donne pas de borne quantitative de mémoire ou de coût, et
ne porte ni sur le continuum, ni sur AC ou CH.

Ce passage accompagne de nouvelles preuves locales. Il n'étend pas la portée
de l'audit historique enregistré pour
`GODEL_INTERNAL_CLOSURE_OBSTRUCTION`. Le rattachement candidat
`GODEL_OPERATIONAL_RUNTIME_CLOSURE_OBSTRUCTION` attend une révision d'évidence
réelle et ses propres revues. Le registre et les passages canoniques existants
restent ceux de leur évidence enregistrée. Aucune revue indépendante nouvelle
n'est revendiquée ici ; aucune traduction anglaise n'est publiée dans ce lot.

## Contrat constitué avant la fermeture

Une source exécutable ne stocke que son rôle et sa profondeur. Elle est indexée
par l'exécution diagonale exacte. Son histoire est l'itération canonique du
générateur à cette profondeur ; son endpoint, ses occurrences et sa différence
sont lus sur cette histoire. La provenance est projetée depuis l'obstruction
héritée par l'histoire et sa conservation est établie par les lois de transport
existantes. Elle n'est pas recopiée depuis le témoin après chaque transition.
Les rôles des pôles ne sont pas les occurrences historiques de production et
de certification.

L'initialisation fixe la profondeur à un. Son histoire est donc exactement la
continuation périmétrale canonique déjà produite, notée H1 dans le plan.
La continuation augmente la profondeur, et son histoire est exactement
l'ancienne histoire prolongée par le générateur. La fermeture conserve le rôle
et la profondeur. Son autorisation positive est décidée par le calcul
`depth = 1` ; elle ne promet aucune collision mémoire. Les événements décrivent
seulement la requête et les profondeurs avant et après l'action. Ils ne
réexposent pas le rôle conservé dans la source. `close` est ici une action
autorisée d'observation terminale qui conserve l'état riche ; le résultat ne
revendique pas qu'elle crée un nouvel état.

Le readout est fixé directement depuis la phrase produite et le rôle, avant
toute fermeture supposée. Il ne passe pas par la présentation circulaire
complète. Des lemmes séparés identifient ces lectures aux extrémités du périmètre
historique ; le pont critique ne consomme pas ces lemmes.

La réalisation identité conserve toute la source comme mémoire et satisfait
toutes les lois d'exactitude par réflexivité. Elle fournit un runtime ouvert
positif, une continuation effective et deux exécutions autorisées de la
fermeture dont les sorties restent distinctes. Séparément, la réalisation
opérationnelle par la profondeur oublie le rôle : elle préserve exactement les
admissions, transitions et événements, et ses deux runs de fermeture ont la
même sortie calculée et les mêmes événements. Elle ne prétend pas préserver le
readout. Le contrat n'est donc ni vide ni déjà contradictoire avant cette loi.

## Action locale et mémoire produite

Le contexte reçu est indexé par l'histoire H1. Ses deux initialisations sont
constituées à partir de la constitution affirmative du même témoin. La
recherche sélectionne sa requête canonique ; l'autorisation fournit un témoin
séparé pour chaque source ; la décomposition produit les deux étapes de cette
même action. Chaque couche est indexée par la valeur de la couche précédente.
Les deux runs sont ensuite construits par les constructeurs inductifs qui
consomment les étapes autorisées. Leurs terminaux et événements ne sont pas des
sorties arbitraires reçues par le contexte.

`GodelOperationalRealizationWithoutRead` sépare localement les lois
d'autorisation, de transition et d'événement de la loi de readout. Le témoin
`godelOperationalGroupingWithoutRead` construit positivement, pour la même
liste singleton non vide, les deux runs, leurs événements égaux et leur mémoire
terminale commune. Il établit ainsi que la différence des rôles n'interdit pas
la collision au niveau opérationnel.

La fermeture sous réalisation complète ajoute la collision des deux sorties
réduites calculées à un contrat qui exige aussi `read_exact`. La mémoire commune
est définie comme la sortie gauche ; la collision identifie la sortie droite à
cette sortie. Il n'existe pas de troisième mémoire reçue avec deux égalités.
Un constructeur de la politique complète produit toutes les autres couches à
partir de cette seule hypothèse, pour la réalisation complète déjà fixée.

Le passage critique compose les terminaux exacts des deux runs, la loi directe
`run_exact` et la collision. Il obtient ainsi l'égalité des deux projections
terminales. Les deux lois `read_exact` donnent directement l'égalité des
readouts terminaux. Ce noyau ne dépend pas de `event_exact`. La stabilité du
rôle le long de toute liste, prouvée par induction depuis la transition, ramène
ces lectures à celles des sources initiales. Les deux branches du readout
donnent alors `Truth(G) = Proof(G)`, sans utiliser de fait négatif sur G.

Le lemme séparé `godelRoleBlindReadExactToEndpointEquality` localise encore la
frontière : sur la réalisation opérationnelle qui fusionne déjà les profondeurs,
la seule adjonction d'une lecture exacte force cette même égalité. Son rejet
consomme ensuite, et seulement ensuite, la vérité et la non-prouvabilité du même
énoncé produit.

L'équivalence de tous les futurs des terminaux est une conséquence parallèle
de l'égalité de leurs projections. Elle n'est pas une prémisse du pont direct.
La conversion `Truth(G) -> Proof(G)` est un transport de types par l'égalité
dérivée. Ce transport mathématique peut être effacé à la compilation : il ne
constitue pas ici un théorème de production physique d'un code de preuve.
Seul le rejet terminal applique cette conversion à la vérité certifiée puis
consomme la non-prouvabilité du même témoin.

## Dépendances et références formelles

La formation conserve l'exécution, les rôles et H1 comme indices. L'exécution
consomme les sources reçues, les étapes autorisées et leur décomposition.
La preuve d'égalité consomme les runs, les lois d'exactitude et la collision.
Le transport historique préserve séparément les occurrences et la provenance ;
le transport mémoire conserve les lectures exigées par le contrat. Aucune
égalité de valeurs n'identifie les occurrences sources.

Les deux modules génériques
[Execution](../RelationalPerimeter/Constitution/Continuation/Execution.lean) et
[CommonMemoryGrouping](../RelationalPerimeter/Constitution/Continuation/CommonMemoryGrouping.lean)
ne connaissent pas Gödel. Ils fournissent les runs exécutés et le regroupement
sous réalisation complète. Le raccord gödelien définit localement
`GodelOperationalRealizationWithoutRead` et
`GodelOperationalGroupingWithoutRead` : cette séparation ciblée évite de
modifier la portée des résultats génériques déjà enregistrés. Le module
générique de regroupement conserve les terminaux exacts, les admissions et
événements réduits, le pont complet `terminalReadEqual` et la branche séparée
`terminalFutureEquivalent`. Un test positif générique construit une collision
exécutée non vide entre deux sources distinctes pour un contrat trivial ; le
témoin gödelien spécialisé construit sa propre collision opérationnelle avant
`read_exact`.

Le [raccord gödelien](../RelationalPerimeter/Constitution/Godel/OperationalClosure.lean)
expose `godelExecutedGroupingToEndpointEquality`, puis le wrapper historique
`godelOperationalClosureToEndpointEquality`, la conversion
`godelOperationalClosureToProducedCompleteness` et les rejets vers `Empty`
puis `False`. `godelExactRuntimeRejectsCommonTerminalMemory` quantifie sur toute
réalisation exacte. L'[instance HA](../RelationalPerimeter/Instances/HeytingArithmetic/OperationalClosure.lean)
spécialise ces résultats à l'unique `heytingArithmeticGodelExecution` existante,
sans hypothèse arithmétique supplémentaire.

Le [contrôle des dépendances](../Tests/GodelOperationalClosureDependencies.lean)
parcourt les constantes des types et des valeurs Lean transitifs des noyaux
critiques. Il refuse les présentations gödeliennes complètes, les totalisations
et contractions, les projections de vérité et de non-prouvabilité, les
éliminations depuis `Empty` ou `False`, les raccourcis par l'équivalence des
futurs et toute dépendance événementielle du pont de readout. Il exige en outre
le témoin positif de collision opérationnelle, vérifie que le schéma des
événements ne contient aucun rôle, puis exige que le rejet final consomme
`read_exact`, `trueWitness` et `unprovable` sans `event_exact`. Un contrôle
distinct maintient le wrapper historique comme application directe du noyau au
regroupement projeté. Ces contrôles mécaniques ne constituent ni une revue du
sens de ce passage, ni un audit indépendant, ni un jugement de nouveauté.

Le résultat existant par totalisation est conservé intégralement. Aucun
théorème ne compare ici ses prémisses avec la nouvelle collision runtime ;
le nouveau raccord n'est donc pas présenté comme un théorème strictement plus
fort. Il expose une autre chaîne de dépendances conditionnelles sous un
contrat de futurs explicite.
