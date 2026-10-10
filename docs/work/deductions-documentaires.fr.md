# Déductions documentaires sous contrat

L'incrément ajoute une capacité précise : utiliser des informations déjà
constituées pour produire une conclusion, puis utiliser cette conclusion dans
un autre calcul, en conservant les sources et permissions de toute la chaîne.
Le [dossier rendu](dossier-fixture-deductions.fr.md) contient les deux citations
produites par le maître, leur différence signée et une somme de cette différence.

Le cas donne `43 − 42 = 1`, puis `1 + 1 = 2`. Les conclusions sont calculées
par des producteurs exécutables. Leurs certificats portent les prémisses
réellement lues. Une conclusion dérivée a un statut distinct d'une citation :
elle ne devient pas une affirmation attribuée au texte reçu.

## Entrées et critère reçus

Le contrat des sources reste `[1, 2]` : la publication de l'occurrence reçue 0
est interdite. Les passages, positions et versions de l'instance précédente
restent identiques. Un **nouveau paramètre déclaré**, le catalogue de
transformations, contient trois occurrences : différence, somme, différence.
Les occurrences 0 et 1 sont permises ; l'occurrence 2 est interdite.
Cette politique additive ne remplace pas le contrat des sources.

Les règles calculent sur les entiers : somme des deux valeurs et différence
« droite moins gauche ». La différence peut donc être négative. Le catalogue
fixe l'opération et son identité ; une référence typée désigne son occurrence.
Une règle égale située ailleurs dans le catalogue ne reçoit pas sa permission
par égalité de contenu.

Le critère d'une conclusion est reçu séparément. Il peut exiger sa valeur,
l'occurrence de la règle et la liste ordonnée des origines de ses prémisses.
Dans le cas construit, la différence doit valoir 1, utiliser la règle 0 et
avoir les origines `[1, 2]`. La somme doit valoir 2, utiliser la règle 1 et
avoir les origines `[1, 2, 1, 2]`. Une bonne valeur avec une mauvaise règle ou
une mauvaise origine échoue au même critère.

Un cas supplémentaire reçoit, dès le départ, une demande de différence 1
avec les origines `[1, 2]`, sans imposer l'occurrence de la règle. Ce critère
reste fixe pendant le refus de la règle 2 et l'exécution de la règle 0.

## Chaîne effectivement construite

`quoteAll` exécute la composition documentaire à partir du curseur reçu.
À chaque étape, **un seul paquet** fournit le prochain curseur, la mémoire du
dossier, la trace et la sortie dont le passage est déposé dans le support de
connaissance. Ce dépôt est une nouvelle incorporation du paquet autorisé :
son producteur capture le contenu de ce paquet et ne relance pas l'extraction.
Le support commence vide dans l'instance concrète.

La déduction possède deux ports vers des occurrences antérieures de ce support.
Son producteur lit leurs valeurs, applique l'opération du catalogue et forme
une nouvelle occurrence. Son action de formation est définie séparément de
l'autorisation. L'admission conserve exactement le support de cette action.
Le reçu et la mémoire suivante lisent ce même support.

Le certificat de la nouvelle occurrence contient les deux justifications
antérieures et la permission de la règle. Il est ainsi possible de dérouler
les sources avec leurs versions et témoins du contrat initial. Lean établit
que leurs positions correspondent exactement aux origines portées par
l'occurrence dérivée. Les références restent des références d'occurrences,
y compris lorsqu'une même conclusion est utilisée deux fois.

La recherche du maître choisit ici les citations. Les déductions utilisent
ses sorties et les producteurs de ressources existants ; les règles et leurs
ports sont explicitement reçus. Cet incrément ne fait pas découvrir les règles
arithmétiques par le maître et ne compte pas une nouvelle tête maître pour
chaque calcul interne. La prochaine recherche documentaire reprend le curseur
effectivement produit par les recherches précédentes.

## Garanties générales et instance fermée

| Garantie | Déclaration principale | Portée |
| --- | --- | --- |
| Déposer le contenu du paquet reçu | `quote_reads_actual_output` | Tout paquet documentaire autorisé |
| Constituer les citations pendant une seule composition | `quoteAll_goal`, `quoteAll_depth`, `quoteAll_occurrences` | Toute liste d'extractions ; accomplissement sous admissibilité positive de chaque paire |
| Calculer depuis les deux ports réels | `FormationAction.value` | Toute règle du catalogue, tout support conforme, toutes références de prémisses |
| Partager le support entre action et admission | `incorporation_uses_actual_resources` | Toute action formée et permission de sa règle |
| Conserver les anciennes lectures et preuves | `FormationAction.transport`, `incorporation_previous_evidence`, `incorporation_previous_goal` | Toute incorporation autorisée d'une déduction |
| Conserver les origines transitives exactes | `Justified.origins_exact` | Toute justification, quelle que soit sa profondeur finie |
| Accomplir le critère dans le résultat réel | `execute_goal` | Permission positive et conformité des valeurs, règle et dépendances au critère reçu |
| Refuser sans effet | `execute_refused` | Permission de règle absente |
| Établir une incompatibilité universelle | `forbidden_rule_incompatible` | Toute mémoire conforme, pour une demande imposant une occurrence de règle interdite |
| Garder le contrat après effacement du contexte | `execute_after_context_erasure` | Tout effacement du contexte auxiliaire, support et politique conservés |

Les [énoncés généraux](../../Tests/LocalAlignment/DocumentaryDeduction.lean) sont
fermés dans une [instance concrète](../../Tests/LocalAlignment/DocumentaryDeductionCases.lean).
Elle exécute la différence, puis la somme de son occurrence fraîche.
Les sources terminales de la somme sont `[1, 2, 1, 2]`, leurs versions
`[1, 2, 1, 2]` et les occurrences de règles utilisées `[1, 0, 0]`.
Cette répétition conserve l'utilisation des mêmes prémisses ; elle n'invente
pas quatre extractions ni trois événements de calcul.

L'occurrence 2 du catalogue permet de former mathématiquement la même
différence 1, mais elle reste interdite à l'incorporation. La mémoire ne change
pas. Aucune mémoire conforme ne peut satisfaire la demande qui impose cette
occurrence. L'effacement du contexte auxiliaire n'autorise pas cette règle.
Pour une demande qui exige la différence 1 et les sources `[1, 2]` sans imposer
l'occurrence de la règle, cette opération interdite répond bien au critère
mathématique. Après son refus et l'effacement du contexte, l'occurrence permise 0
accomplit exactement cette même demande. Le critère et les contrats restent fixes.
Enfin, une nouvelle citation après les deux calculs conserve la conclusion 2
et sa justification exacte.

## Vérification et statut

Le [relevé de vérification](deductions-documentaires-verification.json) identifie
l'arbre de développement, les commandes, les empreintes et leurs verdicts.
La gate complète passe sur 255 fichiers Lean et 22 001 constantes de 254
modules. Les 109 déclarations auditées des deux nouveaux fichiers sont sans
axiome ; l'audit exhaustif ne constate aucune exception dans les déclarations
écrites. Les 364 exceptions générées par le compilateur gardent leur classement
séparé. Les 23 fixtures historiques d'échec attendu restent vérifiées.

Trois clients négatifs temporaires sont aussi refusés par le typage : employer
la conclusion avant sa production, prendre la permission d'une règle égale
pour son occurrence interdite, et présenter une valeur dérivée comme le passage
reçu. Leurs diagnostics et empreintes sont consignés séparément des fixtures
historiques. L'initialisation du certificat de l'exemple a été corrigée pour
consommer sa trace existante ; un lemme de bibliothèque a été remplacé par
une récurrence constructive pour conserver l'absence d'axiome.

Les contrôles exécutables couvrent 24 cas fixes et 864 cas construits depuis
un oracle Python de littéraux reçus : six valeurs possibles pour chacune des
deux sources, huit ensembles de permissions et trois occurrences de règles.
Cela inclut les sources égales, les différences négatives et le refus de la
règle dupliquée. Les cinq audits du client d'exécution sont sans dépendance
interdite. Le corps du Markdown est copié depuis le rendu Lean réel et comparé
à un attendu indépendant.

Le contrôle du C compilé vérifie neuf comptes d'applications avec des frontières
explicites. Il vérifie séparément les deux opérandes effectivement transmis au
calcul et le champ qui conserve le support produit lors de l'admission.
Le certificat de l'exemple lit directement la trace produite ; son initialisation
ne réexécute pas la composition. Trois duplications de producteurs, une
reconstruction du support admis, une inversion des prémisses et une réexécution
dans le certificat, introduites seulement dans la copie en mémoire du C,
sont rejetées par ces contrôles. Ces comptes portent sur le partage annoncé,
sans borne de coût total SAT, mémoire physique ou inférence.

La revendication candidate `DOCUMENTARY_EXECUTABLE_DEDUCTIONS` reste attachée
à cet arbre non commité ; elle n'est pas ajoutée comme évidence figée au registre.
Les résultats de référence Qwen et les anciennes entrées restent inchangés.
Cette étape est une construction et une vérification mathématiques exécutées,
sans nouvelle inférence du modèle.

Les lots 2 et 3 avancent ainsi sur les dépendances effectives. Pour les fermer,
il reste à recevoir une tâche mixte entière, constituer son graphe de
dépendances, définir son admissibilité primitive et prouver l'accomplissement
de son exécution finie. Le lot 4 portera ensuite le progrès malgré toute
politique du modèle. L'oubli documentaire avec équivalence de futurs,
la reprise durable et la comparaison avec/sans gardent leurs obligations
distinctes dans le [plan](plan-alignement-agent-dossier.fr.md).
