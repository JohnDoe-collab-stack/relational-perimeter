# Décision et formation effectives de la citation

Cet incrément poursuit D2 sur `codex/align-persist-recovery`, depuis
`d92583741ed423b6ff95d73002ef484db7ae5a81`, après les
[contrôles des sources](controle-maitre-citation.fr.md). Il ouvre la décision
et la complétion du même maître. La
[spécification v0.3](RP_ALIGN_PERSIST_SPEC_v0_3.fr.md) reste la cible ;
le [plan d'application](application-alignement-persistant.fr.md) conserve
A avant B, puis D3 et D4 après la clôture de D2.

## Ce que les productions alimentent

[ControlCompletion.decideCode](../../Tests/LocalAlignment/DocumentaryControlCompletion.lean)
consomme l'étape de recherche effectivement produite et la mémoire reçue.
Les deux contrôles de source déterminent la graine. Un refus construit sa
décision sans routage, lecture de continuation ni formation de citation.
Sur une graine admise, le calcul construit la continuation d'entrée,
la préservation de cette même étape et sa continuation effectivement retenue.

Le lecteur de continuation parcourt cette donnée sous carburant. Chaque
constructeur `tail` visité et le `head` atteint coûtent une transition.
L'assignation lue est appliquée au même indice du maître. Le bit produit
sélectionne l'occurrence gauche ou droite, avec la permission conservée par
son contrôle. Le candidat n'est pas choisi à partir d'une valeur interchangeable.

[ControlCitation.extractCode](../../Tests/LocalAlignment/DocumentaryControlCitation.lean)
construit le producteur d'extraction reçu, puis lit ses données sources sous
carburant. Ce passage effectivement lu constitue la nouvelle valeur. Les
constructions des valeurs, de la formation positive, du support et de l'action
sont payées séparément. La formation conserve le producteur et la formation
antérieure ; la preuve d'alignement ne relance pas son opération.

La citation est ensuite construite depuis une position payée et une lecture
payée de ce support formé. L'autorisation incorpore ce readout et la permission
du candidat. L'incorporation produit une mémoire et une citation partagées.
Le paquet conserve la continuation, le candidat, l'action, la sortie autorisée,
le résultat incorporé et le témoin d'accomplissement en `Type`.

| Lecture | Dépendance conservée |
| --- | --- |
| Formation | Même producteur, même occurrence source, passage lu et formation antérieure |
| Exécution | Graine, routage, assignation retenue, bit, candidat, ressource puis readout et incorporation |
| Preuve | Égalité des actions et du paquet complet avec les producteurs d'origine ; satisfaction et permission séparées |
| Transport | Même étape maître, mémoire reçue et successeur ; reprise après reset, chargement et oubli vérifiée dans les fixtures existantes |

## Égalités et majorants démontrés

`extractionFromSupport_actual` et `authorizeFromCitation_actual` identifient
les productions entières aux API d'origine. `candidateFromBit_actual` relie
le bit consommé au candidat de cette même étape. `completionFromParts_actual`
porte sur le paquet complet, dont son témoin de tâche accomplie.
Les résultats de `decideCode` et `ControlMaster.runCode` sont typés avec
l'égalité à `Master.decide` et à `Dossier.step`. Le raccord existant conserve
l'égalité à l'étape entière du programme et son progrès en `Type`.

Les bornes couvrent tous les supports, contrats, références et demandes typés
de cette interface. La complétion reçoit une continuation retenue avec son
acceptation ; elle ne reçoit pas une citation déjà produite. La décision
couvre aussi les graines bloquées, sans hypothèse d'accomplissement.

Le majorant du pilote emploie désormais `pairBound`, calculé depuis les deux
références reçues. Trois passages justifient cette enveloppe conservatrice :
la normalisation ne fait pas croître la longueur ; l'ouverture reçue a deux
branches ; le candidat provient de l'une des deux occurrences reçues. Ainsi,
le chemin de lecture retenu et le travail de cette occurrence sont couverts
sans exécuter la recherche ou la décision pour découvrir leur coût.

Les auxiliaires de preuve `completeBound` et `decideBound` décrivent leurs
données intermédiaires. Ils ne sont pas le calcul appelé par le majorant du
pilote. Celui-ci emploie les références, les données des contrôles de source
et le majorant conservateur de la paire. Le coût du calcul de ces majorants,
les allocations et leur réservation restent à établir en D3.

## Portée exacte dans D2

La décision et la formation ne sont plus encapsulées dans un appel entier à
`Master.decide`. Le lecteur de continuation, les traversées de ressources
et de position, la sélection, la formation et les constructions finales sont
raccordés au catalogue déclaré. Le refus ne paie pas les opérations évitées.

La découverte interne de la tête, l'ouverture et la normalisation restent des
appels complexes. La construction de la préservation et son application à la
continuation, ainsi que l'application de l'assignation, sont maintenant des
frontières nommées distinctes ; leurs calculs internes et appels différés
restent à instrumenter. Ces transitions ne sont pas des bornes physiques
constantes de ces fonctions.

L'assemblage de citation appelle encore `quotationStep`. Les assemblages
d'entrée manquante, la restauration des frames, les lectures différées de
liaisons et de justification, la composition, les traces et les allocations
de l'interprète restent ouverts. **D2 entier, CONT-03 et P15 restent ouverts.**
Les majorants ici démontrés ne constituent pas encore l'enveloppe complète
du secours exigée par CTRL-02.

## Vérifications de développement

Les matrices de carburant vérifient les valeurs, les origines, les permissions
et les traces littérales. Elles incluent les seuils exacts, un carburant
insuffisant et un surplus. Les nouvelles matrices portent sur les trois
formations sources, leurs readouts, trois chemins de continuation et trois
décisions : citation autorisée, regroupement et refus. Les scénarios de reprise
et d'oubli emploient les mêmes productions reçues que précédemment.

Les seuils du catalogue deviennent **106, 84 et 176** pour la citation de
référence, le refus à origine interdite et la citation révisée. Ils incluent
encore les frontières complexes annoncées ; aucun gain de coût total n'en
est déduit. Les deux décisions positives testées coûtent 23 transitions
de décision ; le refus coûte 2 et ne forme aucune citation.

Une attente de développement avait placé la continuation positive en seconde
position dans la paire non regroupée. La normalisation échange cette paire
et place la branche acceptée en tête. Les trois lemmes
`baseline_routing_reads_head`, `grouped_routing_reads_head` et
`revised_routing_reads_head` prouvent cette lecture d'une seule cellule.
Les attentes ont été corrigées à partir de ces définitions et preuves ; les
sources exécutées n'ont pas été modifiées pour obtenir cette trace. Les
échecs provisoires et leurs empreintes restent conservés hors du dépôt.
Cette qualification demeure un travail de développement, sans run confirmatoire.

Le [contrôle C de complétion](../../scripts/check-documentary-completion-codegen.py)
vérifie les corps et captures nommés : étape, graine, continuation, bit,
occurrence, permission, producteur, formation, readout et résultat partagés.
Il vérifie aussi que les majorants du pilote ne lancent pas ces producteurs.
Il rejette 105 mutations textuelles. Les six gardes raccordées rejettent
427 mutations au total ; ce sont des tests des gardes, sans binaires mutants
ni audit exhaustif du graphe d'appels.

Le [relevé de cet incrément](controle-completion-citation-verification.json)
porte les commandes, empreintes et résultats. Les relevés précédents gardent
leurs résultats historiques. Aucun nouveau run de modèle ni audit indépendant
n'est revendiqué.

La première gate exhaustive a rejeté les dépendances axiomatiques introduites
par l'automatisation des preuves arithmétiques des majorants. Ces preuves ont
été réécrites par composition de lemmes constructifs sur les naturels et
réécriture d'égalités. Les définitions exécutées, les scripts et les attentes
de traces sont restés identiques. L'échec initial, ses diagnostics et les
empreintes des deux états sont conservés dans la qualification.

La gate complète après cette correction a réussi : **314 fichiers Lean,
313 modules et 26 229 constantes**, sans exception pour une déclaration
écrite. Les 224 audits explicites des seize modules de contrôle sont sans
axiome. Les matrices de l'interprète et de l'arithmétique donnent 8 959
verdicts, avec 40 audits d'exécution propres ; les six gardes C rejettent
leurs 427 mutations textuelles. Les 23 fixtures de rejet attendu produisent
exactement leurs diagnostics et emplacements prévus.
