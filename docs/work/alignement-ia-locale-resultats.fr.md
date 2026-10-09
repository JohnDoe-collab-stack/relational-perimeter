# Premier raccordement réel : propositions d'une IA, oubli et contrat persistant

Le raccordement fonctionne avec un modèle local réel. Qwen3 4B propose les
opérations ; la machine constitutive les exécute sous son contrat reçu. Dans
l'expérience confirmatoire, quatre effacements du contexte du modèle n'ont
empêché ni la poursuite de la production ni le maintien des permissions et des
critères de réponse. Toutes les réponses opérationnelles proviennent du noyau
Lean et le rejeu des reçus est exact.

Ce résultat expérimental accompagne une preuve plus générale : le raccordement
accepte une politique de proposition adaptative quelconque. Sa conformité ne
dépend donc pas de la qualité des douze choix observés chez Qwen.

## Ce qui est démontré

Le client formel est [ModelLoop.lean](../../Tests/LocalAlignment/ModelLoop.lean).
Il reçoit une politique, un contexte, une entrée et une observation du présent.
La politique peut demander une remise à zéro du contexte ; elle n'a aucun
constructeur lui permettant de remplacer la mémoire machine ou le contrat.
Une proposition incorporée consomme le producteur existant
`executeProducedInput`, dont le résultat partagé forme l'état suivant, l'événement
et les témoins de réponse. Un rejet de protocole laisse la mémoire intacte.

| Déclaration | Conclusion exacte |
| --- | --- |
| `certifyRun` | Pour toute politique, tout état et toute suite finie d'entrées, construit les témoins de chaque étape réelle d'incorporation ou de rejet. |
| `accepted_entire_producer` | Le raccordement consomme le producteur de ressources existant, avec son résultat et son `RequestEvidence`. |
| `all_adaptive_requirements` | Le contrat reste identique après toute suite finie de choix adaptatifs, y compris les remises à zéro du contexte. |
| `all_adaptive_old_reads` | Les lectures des occurrences déjà constituées restent identiques après ces suites. |
| `permitted_obtain_answer` | Une demande permise produit le travail nécessaire et rend la valeur autorisée de l'occurrence demandée. |
| `initial_profile_not_recoverable_combined` | À contexte initial du modèle fixé, aucun récupérateur uniforme ne retrouve le profil source depuis l'état composé. |
| `forgotten_profiles_same_adaptive_run` | À politique, contexte et entrées identiques, deux sélections initiales normalisées conduisent à la même exécution adaptative. |

L'autorisation consomme une référence de permission, une référence d'occurrence
et l'égalité avec la lecture de cette occurrence. Les témoins d'origine relient
cette occurrence à la normalisation effectivement exécutée ou à une production
de continuation. La préservation du contrat et des anciennes lectures se
compose avec cette génération ; elle n'impose pas l'immobilité de l'état.

Le [noyau de transport](../../Tests/LocalAlignment/Kernel.lean) apporte également
une preuve pour toute suite finie de lignes brutes :
`all_raw_inputs_requirement` et `all_raw_inputs_old_reads`. Une entrée qui échoue
au décodage ne modifie pas la mémoire (`decode_failure_no_effect`). Les audits
des 34 déclarations de ce noyau, y compris les parseurs, la sérialisation et
`main`, sont sans axiome. Les 23 déclarations auditées du raccordement adaptatif
le sont aussi.

## Ce qui a réellement été exécuté

Le [protocole figé](../../apps/local-alignment/evidence/protocol.json) fixe les
sources Lean et Python, les poids, le runtime, les paramètres, les graines et
les demandes avant le run. Les sources existantes partent de `main`, révision
`b71904ab3b1cabb18faec791a690fa87b434e00e` ; les nouveaux fichiers sont identifiés
par leurs empreintes dans ce protocole. Les preuves nouvelles ne sont pas encore
des entrées figées du registre scientifique.

Le modèle est le
[Qwen3 4B GGUF officiel](https://huggingface.co/Qwen/Qwen3-4B-GGUF), révision
`bc640142c66e1fdd12af0bd68f40445458f3869b`, avec les poids `Q4_K_M` vérifiés par
SHA-256. Le runtime est
[llama.cpp b11524](https://github.com/ggml-org/llama.cpp/releases/tag/b11524),
édition Windows Vulkan vérifiée, exécutée sur la carte graphique locale. Aucune
API d'inférence distante n'intervient. Les téléchargements, journaux du serveur
et textes bruts du modèle restent hors du dépôt.

Le [résumé machine](../../apps/local-alignment/evidence/summary.json) et les
[reçus dérivés](../../apps/local-alignment/evidence/receipts.json) donnent :

| Observation | Résultat |
| --- | --- |
| Appels réels au modèle | 12 |
| Effacements de son historique de messages | 4 |
| Étapes constitutives effectivement produites | 8 |
| Réponses autorisées | 7 |
| Réponses obtenues immédiatement après effacement | 3 |
| Réponses utilisant une occurrence déjà présente, sans nouvelle production | 4 |
| Refus hors portée | 2 |
| Refus de valeur incorrecte | 1 |
| Refus d'une occurrence absente | 1 |
| Avance demandée et exécutée | 1 |
| Rejeu dans une nouvelle session Lean | Exact pour les 12 reçus |

Le transcript est effectivement vidé avant chaque demande marquée par un
effacement : aucun ancien message n'est renvoyé au modèle lors de cette demande.
L'observation courante du noyau reste disponible. L'effacement ne recrée pas la
machine et ne réinjecte pas sa sélection initiale. Une demande autorisée produit
ensuite les occurrences manquantes à partir du présent retenu.

L'expérience ne corrige pas les choix du modèle pour obtenir ces résultats.
Ainsi, sa dernière proposition emploie `propose` plutôt que l'`obtain` demandée
en langage naturel ; elle est hors portée et le noyau la refuse. Le suivi exact
de toutes les instructions humaines n'est donc pas établi par ce run. Le
progrès, les réponses après oubli et les refus requis ont tous été obtenus.

## Vérifications et lecture du résultat

Les tests de transport ont vérifié 14 lignes, dont des requêtes malformées, des
arguments surnuméraires, des dépassements de ressources et les trois refus
fondés. Six formes JSON incorrectes sont également rejetées par l'encodeur.
La répétition des 14 lignes avec l'autre sélection initiale valide donne
exactement les mêmes reçus.

La lecture du C généré retrouve un seul appel au producteur existant dans la
branche incorporée de `dispatchCertified`, et un seul appel à ce dispatch dans
`process`. Les composantes du résultat servent à la continuation et à la
sérialisation. Ce contrôle de code généré complète la lecture des définitions
Lean ; il ne constitue pas un théorème sur le compilateur ou le matériel.

Le run initial a été conservé. Un second protocole a été figé puis exécuté après
le classement final des deux modules dans la couche expérimentale `Tests`, comme
les runners machine existants. C'est ce second run qui est livré ici. L'import
ajouté à `Tests.AllConstantsAudit` soumet ces modules à l'audit exhaustif des
constantes du dépôt. Les contrats, les producteurs de production et les
empreintes des affirmations existantes restent ceux de `main`.

La gate complète `scripts/verify.ps1` a réussi sur cet arbre : 246 fichiers Lean,
20 868 constantes dans 245 modules, aucune exception écrite, 23 fixtures de
refus attendu, contrôles des dépendances et du code généré. Les contrôles
documentaires passent pour les 18 affirmations existantes et leurs 81
déclarations ; leurs statuts de revue restent ceux du registre. La vérification
statique finale inclut les liens des documents de ce chantier.

## Ce que cette étape ferme et ce qui suit

On a un passage réel du modèle local à l'activité certifiée du projet, avec
persistance du contrat après oubli du contexte, refus justifiés et progrès
positif. Le modèle peut se tromper ; ses erreurs de proposition ne deviennent
pas des réponses autorisées. La garantie porte sur les effets et les messages
de la machine composée.

L'expérience actuelle accomplit des demandes de production et de lecture
d'occurrences sous une portée reçue. Pour avancer vers une application d'IA
plus large, il faut définir la tâche utile suivante, ses actions effectives,
son contrat, son critère d'accomplissement et les oublis qu'il autorise. Chaque
nouvel effet devra être raccordé à un producteur et à ses préservations. Cette
extension devra garder le progrès dans le contrat, afin qu'une conformité
obtenue en refusant tout ne puisse satisfaire la cible.

La [cible de chantier](alignement-ia-locale-cible.fr.md) et les
[commandes de reproduction](../../apps/local-alignment/README.fr.md) rendent ces
obligations explicites. Le serveur local a été arrêté après les expériences ;
ses poids vérifiés restent disponibles pour les prochaines exécutions.
