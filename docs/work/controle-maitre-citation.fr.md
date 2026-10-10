# Contrôles des sources dans le maître de citation

Cet incrément poursuit D2 du [plan d'application](application-alignement-persistant.fr.md)
sur `codex/align-persist-recovery`, depuis
`d92583741ed423b6ff95d73002ef484db7ae5a81`. Il ouvre les contrôles documentaires
de la citation ; il ne clôt pas les calculs internes des moteurs du maître.
La [spécification v0.3](RP_ALIGN_PERSIST_SPEC_v0_3.fr.md) reste inchangée.

## Chaîne effectivement exécutée

[ControlSelection.checkCode](../../Tests/LocalAlignment/DocumentaryControlSelection.lean)
calcule la position de la référence reçue et recherche la permission, en
conservant la première occurrence autorisante. En cas d'absence, il produit le
contrôle rejeté sans lecture du passage. Sinon, une traversée payée lit le
passage effectivement conservé. Cette position et cette lecture constituent
la citation contrôlée.

Trois comparaisons portent sur le fait, la valeur et l'origine demandée.
L'absence d'origine imposée est traitée explicitement. Les comparaisons
naturelles utilisent l'interprétation structurale déjà instrumentée ; les
contrôles ne délèguent pas leur décision à `meetsDecision` ou à `Selection.check`.
La permission et la satisfaction de la demande restent des conditions séparées.

`check_bounded` couvre toutes les sources, tous les contrats, demandes et
références typés de cette interface. Son majorant compose les traversées de
position, permission et passage, puis les comparaisons et constructions. Il
peut surestimer une branche rejetée. Le calcul de ce majorant lit encore des
données avec les auxiliaires natifs : son propre bootstrap reste une obligation
de D3, distincte de la borne d'évaluation démontrée ici.

[ControlMaster.searchCode](../../Tests/LocalAlignment/DocumentaryControlMaster.lean)
conserve la tête du maître reçue de sa production réelle. Les contrôles gauche
et droit construits déterminent la formule. Cette formule, le même indice
sélectionné, l'ouverture réelle et sa réduction sont transmis à
`Master.stageFromParts`. L'égalité `stageFromParts_actual` porte sur toute
l'étape de recherche d'origine, pas seulement sur ses flags ou son readout.

La décision consomme cette même étape et la mémoire reçue. Son paquet est
prouvé égal à `Dossier.step`. L'assemblage dans `ControlStep.code` consomme le
paquet conservé ; il n'exécute plus `Dossier.step` dans sa fermeture de citation.
L'égalité avec l'étape entière de `Program.step`, dont le progrès reste en
`Type`, est conservée. Aucune autre instance maître n'est créée.

| Lecture | Dépendance employée |
| --- | --- |
| Formation | Références reçues, support des sources, permission distincte et occurrence effectivement lue |
| Exécution | Comparaisons payées, tête existante, contrôles effectifs, formule puis ouverture et réduction réelles |
| Preuve | Égalités avec les contrôles, l'étape de recherche, le paquet documentaire et l'étape du programme d'origine |
| Transport | Même mémoire et même successeur issus du paquet ; reset et chargement du contrôle gardent ces données |

## Frontières encore ouvertes

Les étiquettes `citationHead`, `citationOpening`, `citationReduction` et
`quotationProducer` entourent encore des appels complexes. La production
interne de la tête comprend découverte, filtrage, application, décomposition,
construction du support et continuation. L'ouverture et la normalisation
contiennent leurs propres parcours et calculs. La complétion comprend le
transport de continuation, la sélection, l'extraction, l'autorisation et
l'incorporation. Les nommer séparément ne compte pas encore tous leurs coûts.

L'assemblage de citation utilise encore `quotationStep`. Les assemblages
d'entrée manquante, la restauration de frame, les appels différés de liaisons
et justification, `Code.bind`, les traces, paquets et allocations restent
également à raccorder. Les unités actuelles sont celles du catalogue abstrait,
avec les frontières natives déclarées. Aucun coût physique constant des appels
complexes ou des entiers non bornés n'est affirmé.

**D2 n'est donc pas terminé.** Cette ouverture doit être poursuivie dans ces
mêmes producteurs et moteurs, avant les enveloppes de D3 et les tours bornés
de D4. Les preuves existantes restent établies dans leurs portées respectives.

## Vérifications de développement

Le [smoke documentaire](../../scripts/run-documentary-interpreter-smoke.py)
fixe les attentes de valeur, origine, permission, trace et carburant avant
son exécution. Huit matrices supplémentaires de source couvrent refus avant
lecture, fait et valeur erronés, origine imposée, permission dupliquée,
contrat vide et deux occurrences de même passage. Elles produisent 800 verdicts.
Les citations sont aussi vérifiées depuis un préfixe, après reset, après
chargement du contrôle et après oubli de deux histoires sources distinctes.

Les seuils exacts du catalogue actuel sont 83 pour la citation de référence,
82 pour la demande à origine interdite et 150 pour la citation révisée.
Leurs traces incluent les contrôles nouvellement ouverts ; les coûts des
appels complexes décrits ci-dessus restent séparés. Les tests ne mesurent
pas un gain de performance et ne constituent pas une nouvelle comparaison
du modèle local.

Le [contrôle C du maître](../../scripts/check-documentary-master-control-codegen.py)
examine les corps et captures nommés : lecture après permission, citation
construite depuis les données lues, choix du même indice et des deux flags,
conservation de tête, contrôles, ouverture et réduction, puis décision sur
l'étape et la mémoire reçues. Ses 62 mutations textuelles sont rejetées.
Il est consommé par la gate existante de l'interprète. Sa portée n'est ni un
audit exhaustif du graphe d'appels ni l'exécution de binaires mutants.

Les commandes, empreintes, résultats complets et obligations ouvertes figurent
dans le [relevé de cet incrément](controle-maitre-citation-verification.json).
Les résultats antérieurs ne sont pas réétiquetés ; aucun audit indépendant ni
run supplémentaire de modèle n'est revendiqué.

La gate complète `scripts/verify.ps1` a réussi sur 312 fichiers Lean et
26 099 constantes dans 311 modules, avec zéro exception écrite et 23 fixtures
de refus attendu conformes. Les 189 audits explicites des quatorze modules
de contrôle sont sans axiome. Les deux smokes du contrôle produisent
7 459 verdicts : 2 147 documentaires et 5 312 arithmétiques, avec 31 audits
runtime sans axiome. Les cinq gardes C du contrôle rejettent 318 mutations.
Les sources Lean et scripts sont restés identiques à leurs empreintes figées
avant cette gate. Ce résultat qualifie l'incrément décrit ; les frontières
ouvertes ci-dessus restent ouvertes.
