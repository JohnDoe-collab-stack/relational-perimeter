# Une IA locale raccordée à l'exécuteur constitutif

Le modèle choisit des propositions. Le noyau Lean produit les réponses et les
actions autorisées sous le contrat reçu. Le contexte du modèle peut être effacé
pendant la tâche : l'exécuteur conserve sa mémoire et son contrat.

## État du chantier au 10 octobre 2026

Le [plan documentaire](../../docs/work/plan-alignement-agent-dossier.fr.md)
porte le suivi actuel. Les sections suivantes décrivent les incréments et
leurs procédures de reproduction ; leurs relevés gardent les empreintes et
les statuts de leur vérification propre.

| Partie | État actuel |
| --- | --- |
| Raccord Qwen existant | Réalisé sur le noyau `Agent`, avec effacements de contexte et rejeu exact |
| Chaîne documentaire | Extractions et déductions sur ports réels, critères indépendants et accomplissement de tout programme admissible de la classe finie à ordre reçu |
| Continuation et oubli | Progrès pour toute politique totale, accord de tous les futurs finis déclarés et checkpoint du présent typé prouvés |
| Reprise sur disque | Préfixe concret et dernière somme restaurés dans un nouveau processus, avec fidélité des formations et mêmes fichiers que l'exécution continue |
| Stockage documentaire | Égalité exacte depuis des octets pour les stockages canoniques des exécutions finies de programme, de politique adaptative et de requêtes mémoire ; reprise et nouvelle déduction dans 16 cas physiques |
| Suite du lot 6 | Présent adaptatif complet et ressources maître à restaurer ; accord des futurs depuis les octets et interface documentaire Qwen à fermer |
| Lot 7 | Comparaisons avec/sans et livraison documentaire à réaliser |

La fidélité du stockage canonique est désormais prouvée depuis des octets,
y compris ses formations et ses lecteurs de justification. L'accord général
des futurs du présent complet concerne encore le présent typé. La prochaine étape relie ces lois à la
restauration complète depuis un fichier, puis permet de nouvelles citations
et déductions. Le modèle local devra ensuite proposer les actions de cette
interface documentaire.

Le lot utilise [Qwen3 4B GGUF officiel](https://huggingface.co/Qwen/Qwen3-4B-GGUF),
révision `bc640142c66e1fdd12af0bd68f40445458f3869b`, quantification `Q4_K_M`, avec
[llama.cpp b11524](https://github.com/ggml-org/llama.cpp/releases/tag/b11524).
Les poids et le runtime sont téléchargés et vérifiés hors du dépôt, sous
`$env:LOCALAPPDATA\relational-perimeter\local-ai`. L'inférence reste sur
`127.0.0.1`. Aucun compte ni clé API n'est nécessaire.

## Reproduire

Depuis la racine, avec PowerShell, Python 3 et la toolchain Lean du dépôt :

```powershell
lake build +Tests.LocalAlignment.Kernel
lake env lean Tests/LocalAlignment/Kernel.lean
python -B apps/local-alignment/run.py test-transport
pwsh -NoProfile -File apps/local-alignment/start-local.ps1
```

Le lancement initial télécharge environ 2,5 Go de poids et 33 Mo de runtime.
Attendre que `http://127.0.0.1:18434/health` indique `ok`. La configuration utilise
Vulkan, un contexte de 4096 tokens, un slot et le raisonnement désactivé.

Figer un protocole neuf **avant** chaque expérience confirmatoire, puis conserver
ses sorties brutes hors du dépôt. La même commande de gel refuse d'écraser un
protocole existant. Le run refuse des sources ou paramètres différents.

```powershell
$cache = Join-Path $env:LOCALAPPDATA 'relational-perimeter\local-ai'
$protocol = Join-Path $cache 'protocol-first-local.json'
$output = Join-Path $cache 'runs\first-local'
python -B apps/local-alignment/run.py freeze --protocol $protocol
python -B apps/local-alignment/run.py confirm --protocol $protocol --output $output --model-file (Join-Path $cache 'Qwen3-4B-Q4_K_M.gguf') --runtime-archive (Join-Path $cache 'llama-b11524-bin-win-vulkan-x64.zip')
python -B apps/local-alignment/run.py replay --transcript (Join-Path $output 'transcript.json')
pwsh -NoProfile -File apps/local-alignment/start-local.ps1 -Stop
```

Le protocole fixe les sources Lean, le raccord Python, les réglages, les graines,
les douze demandes et les quatre effacements de contexte. Les réponses du modèle
ne sont pas remplacées par un scénario préprogrammé. Un choix inadapté reste
enregistré ; si les observations requises manquent, l'expérience échoue.

## Preuve et exécution

[ModelLoop.lean](../../Tests/LocalAlignment/ModelLoop.lean) quantifie
sur toute politique adaptative et toute suite finie d'entrées. `certifyRun`
construit les témoins de chaque incorporation ou rejet. Le contrat persiste,
les anciennes lectures restent stables et `obtain` permise accomplit les étapes
nécessaires. À contexte initial fixé, la sélection de profil oubliée reste
uniformément irrécupérable depuis l'état composé.

[Kernel.lean](../../Tests/LocalAlignment/Kernel.lean) traite les lignes ASCII en données, puis consomme le
même `dispatchCertified`. La réponse JSON est sérialisée depuis cette production
et ses témoins. Toutes les déclarations auditées, y compris le parseur, la
sérialisation et l'entrée `main`, sont sans axiome. Le noyau est exécuté avec
`lake env lean --run` ; aucun argument `native_decide` ni bibliothèque JSON
introduisant des axiomes n'entre dans le passage.

[run.py](run.py) demande une proposition au modèle, l'encode et transmet une
ligne au noyau. Il vérifie ensuite la cohérence des reçus et les rejoue exactement
dans une nouvelle session Lean. La décision d'autorisation appartient au noyau.
Une autre sélection initiale valide fait aussi l'objet du test de transport :
les mêmes requêtes doivent produire exactement les mêmes reçus.

## Portée

Le contrat concret porte sur les lectures d'occurrences constituées, avec une
portée singleton dans cette interface. Les observations comprennent les étapes
effectivement produites, des refus justifiés, la réutilisation d'une occurrence
et la poursuite après effacement du contexte du modèle. Une remise à zéro du
transcript ne promet ni l'effacement physique de la RAM ou du cache du serveur,
ni l'égalité des choix du modèle avant et après oubli.

Les états de découverte, les permissions, les références et les origines restent
ceux de la machine existante. Ce lot n'établit pas un nouveau solveur SAT général
ou un minimum physique de mémoire. La tâche plus large et les prochaines
obligations sont fixées dans la
[cible du chantier](../../docs/work/alignement-ia-locale-cible.fr.md).

Comme les runners machine existants, ce premier raccordement est un client
expérimental dans `Tests`. Il emploie les producteurs de `main` ; le façonnage
d'une nouvelle interface publique et son enregistrement scientifique constituent
un lot d'intégration distinct. Ses deux modules entrent dans l'audit exhaustif
du dépôt, y compris leurs constantes privées et les parseurs générés.

## Premier incrément documentaire

La [couche documentaire](../../docs/work/premiere-couche-documentaire.fr.md)
construit une extraction depuis les sources reçues, avec références typées,
permissions et critère d'accomplissement indépendant. Les cas construits
éprouvent une autre voie autorisée et une demande incompatible avec le contrat,
y compris après effacement du contexte.

```text
lake build Tests.LocalAlignment.DocumentaryCases
python -B scripts/run-documentary-smoke.py
python -B scripts/check-documentary-codegen.py
```

Le smoke est un cas de développement sans appel au modèle. Les incréments
suivants ont relié cette opération à la recherche du maître et fermé les
futurs du présent typé. La reprise durable complète reste au lot 6.

## Raccord documentaire à la recherche du maître

Le [raccord sémantique](../../docs/work/raccord-documentaire-maitre.fr.md)
traduit un choix entre deux occurrences reçues en un problème SAT, avec
équivalence exacte entre satisfaction, fait demandé et permission.
Une seule tête du maître fournit la variable découverte et le successeur.
L'ouverture et le regroupement existants déterminent le transport ; le bit
effectivement retenu choisit la source dont le passage est ensuite extrait.

```text
lake build Tests.LocalAlignment.DocumentaryMasterCases
python -B scripts/check-documentary-master-codegen.py
python -B scripts/run-documentary-master-smoke.py
```

Ce smoke de développement couvre les origines, les fronts retenus, les deux
cas d'interdiction après effacement du contexte et la continuation depuis
le successeur produit. Les dépendances et l'ordonnanceur documentaire sont
maintenant constitués ; leur raccord au modèle local reste au lot 6.

## Composition de plusieurs demandes

La [composition finie](../../docs/work/composition-dossier-maitre.fr.md)
transmet à chaque demande le successeur et la mémoire réellement produits.
Pour toute liste dont chaque demande possède une source permise dans sa paire
reçue, Lean construit l'accomplissement du dossier entier. Les références et
témoins antérieurs sont conservés ; la reprise depuis un préfixe produit donne
le même état et les mêmes événements que l'exécution continue.

```text
lake build Tests.LocalAlignment.DocumentaryDossierCases
python -B scripts/check-documentary-dossier-codegen.py
python -B scripts/run-documentary-dossier-smoke.py
```

Le smoke exécute 21 contrôles concrets et 680 cas construits depuis un oracle de
littéraux reçus. Il rend le dossier réellement constitué. Les déductions et
la continuation adaptative sont construites dans les incréments suivants ;
l'interaction documentaire avec Qwen reste à réaliser.

## Déductions sur les éléments constitués

La [chaîne de déduction](../../docs/work/deductions-documentaires.fr.md)
dépose les sorties autorisées du maître dans un support d'occurrences. Un
producteur lit deux ports de ce support et calcule une somme ou une différence
signée. La conclusion, son certificat et la mémoire suivante partagent la même
ressource produite. Les règles ont leur propre catalogue reçu et leurs permissions.

```text
lake build Tests.LocalAlignment.DocumentaryDeductionCases
python -B scripts/check-documentary-deduction-codegen.py
python -B scripts/run-documentary-deduction-smoke.py
```

Le smoke de développement couvre 24 contrôles concrets et 864 cas selon les
faits reçus et les permissions des règles. Il rend la chaîne citation,
différence, puis somme de cette conclusion. La continuation après les déductions
conserve leurs valeurs et justifications. Le langage mixte fini est constitué
dans l'incrément suivant, puis complété par l'ordonnanceur adaptatif. Le raccord
documentaire à Qwen reste ouvert.


## Programmes mixtes reçus et accomplissement global

Les [programmes documentaires](../../docs/work/programmes-documentaires-mixtes.fr.md)
entrelacent extractions et déductions avec des références typées vers les
sorties antérieures. Pour tout programme admissible de ce langage fini depuis
un état initial complet, la trace réelle fournit la preuve d'accomplissement
de toutes ses sorties. Les permissions et lois de compatibilité reçues
n'apportent ni solution achevée ni exécution.

```text
lake build Tests.LocalAlignment.DocumentaryProgramCases
python -B scripts/check-documentary-program-codegen.py
python -B scripts/run-documentary-program-smoke.py
```

Le smoke couvre 26 contrôles fixes et 1 536 programmes construits. Une
production autorisée mais incorrecte reste utilisable ; son objectif reste
insatisfait. Un refus laisse une dépendance manquante, puis une opération
indépendante peut continuer. Le rendu provient des productions réelles.
L'ordre des tâches est reçu. La continuation adaptative est construite dans
l'incrément ci-dessous, puis complétée par les lois documentaires d'oubli.
La reprise durable complète reste au lot 6.

## Continuation adaptative et progrès indépendant des propositions

La [continuation documentaire](../../docs/work/continuation-documentaire-adaptative.fr.md)
reçoit désormais une politique arbitraire de proposition. Chaque tour traite
au plus une proposition, puis accomplit l'obligation courante lorsqu'elle
n'a pas été réalisée par cette proposition. Pour tout programme admissible
de la classe finie reçue, n obligations prennent exactement n tours contrôlés
et au plus 2n tentatives d'étape. Les lectures répétées et les absences ne
peuvent pas laisser indéfiniment cette obligation en attente.

```text
lake build Tests.LocalAlignment.DocumentaryAdaptiveCases
python -B scripts/check-documentary-adaptive-codegen.py
python -B scripts/run-documentary-adaptive-smoke.py
```

Les propositions utiles peuvent modifier la recherche de source ; les
productions supplémentaires permises restent dans le support avec leurs
justifications. Le contexte peut être remis à zéro à chaque tour ; les
ressources, liaisons, obligations et compteur continuent. Ce smoke emploie
des politiques construites et un oracle indépendant. Le raccord documentaire
au modèle local et le checkpoint complet sur disque restent ouverts. Le
contrat de futurs est fermé pour le présent typé dans l'incrément ci-dessous ;
un premier cas physique de dernière déduction est également réalisé.


## Présent documentaire et futurs après oubli

Les [lois de mémoire documentaire](../../docs/work/memoire-documentaire-et-futurs.fr.md)
étendent le présent par des tables finies de liaisons et construisent l'accord
riche/réduit pour toute suite finie de requêtes déclarées. Les événements,
lectures, admissions positives et possibilités d'accomplissement concordent.
L'archive de propositions réellement reçues est retirée ; les occurrences,
leurs formations, justifications, permissions, obligations et compteur restent
conservés. Deux anciennes propositions deviennent irrécupérables dans ce contrat.

```text
lake build Tests.LocalAlignment.DocumentaryMemoryCases
python -B scripts/check-documentary-memory-codegen.py
python -B scripts/run-documentary-memory-smoke.py
```

Le checkpoint typé restitue le présent courant et les tâches restantes ;
une version inconnue est rejetée. Le smoke couvre 19 contrôles fixes et 648
cas de politique, reset et checkpoint, dont 72 cas de règle imposée interdite.
Cette vérification n'effectue aucun nouvel appel au modèle. Le premier codec
portable et la reprise physique sont réalisés dans le cas décrit ci-dessous.
Le présent adaptatif complet et l'accord de ses futurs depuis les octets
restent à fermer avec le lot 6 ; le lot 5 demeure ouvert sur cette obligation durable.


## Premier checkpoint documentaire sur disque

Le [raccord portable](../../docs/work/checkpoint-documentaire-portable.fr.md) restaure les formations du préfixe documentaire
réel et effectue sa dernière déduction dans un nouveau processus. Les octets du
dossier et des ressources finales sont identiques à l'exécution continue.
Le test comprend 20 refus de checkpoints invalides et conserve les identités
de deux occurrences de même valeur. Il est intégré à la gate complète.

La portée est un schéma fixé après les trois citations, avec une seule somme
restante. La reprise du présent adaptatif complet et du curseur maître reste
ouverte ; cet incrément ne lance pas de nouvel essai Qwen.

```text
lake build Tests.LocalAlignment.DocumentaryPortableCases
python -B scripts/check-documentary-checkpoint-codegen.py
python -B scripts/run-documentary-checkpoint-smoke.py
python -B apps/local-alignment/documentary-checkpoint.py start mon-espace
python -B apps/local-alignment/documentary-checkpoint.py resume mon-espace
```

Les deux dernières commandes terminent des processus distincts. La reprise
lit `mon-espace/checkpoint.bin` et écrit `mon-espace/dossier.md` ainsi que les
ressources finales. Pour l'agent complet, la sauvegarde devra également porter
la mémoire du dossier, les ressources maître, la file restante, les liaisons,
le contexte de politique et les observations conservées, avec leur preuve
de restauration fidèle et l'accord des futurs déclarés.

## Restauration générale du stockage canonique

Le [rapport du stockage](../../docs/work/restauration-stockage-documentaire.fr.md)
décrit les preuves générales pour les programmes finis, les politiques
adaptatives totales et les requêtes mémoire déclarées. Les octets restituent
le stockage dépendant exact sous la même configuration reçue. Les refus,
les productions supplémentaires et les sorties autorisées qui manquent leur
but font partie de cette preuve.

Le schéma 2 porte ce stockage seul. Il est distinct du premier checkpoint à
quatre slots ; aucun des deux ne recharge le curseur maître. Les tests lancent
45 processus : 16 sauvegardes, leurs 16 reprises avec nouvelle déduction et
13 refus de fichiers altérés. Ils restent des smoke tests sans inférence Qwen.

```text
lake build Tests.LocalAlignment.DocumentaryPortableStoreCases
python -B scripts/check-documentary-portable-store-codegen.py
python -B scripts/run-documentary-portable-store-smoke.py
```

## Restauration des composants du présent

Le [raccord des composants](../../docs/work/restauration-present-composants.fr.md)
restaure le curseur maître entier et le présent complet depuis un payload
typé matérialisé, avec leurs formations, producteurs et futurs. Le schéma 3
recharge aussi la mémoire du dossier depuis des octets, avec son lecteur de
justification exact. Les tests vérifient 16 reprises physiques de ce composant,
12 refus et une continuation du présent typé avec citation maître et somme.

Les fonctions et données maître n'ont pas encore de codec portable complet.
Les données de contrôle ont désormais le codec décrit ci-dessous. La reprise du présent entier
depuis un fichier reste donc ouverte ; les tests de composant ne la clôturent pas.

```text
lake build Tests.LocalAlignment.DocumentaryRestorationComponentsCases
python -B scripts/check-restoration-components-codegen.py
python -B scripts/run-restoration-components-smoke.py
```

## Contrôle documentaire depuis des octets

Le [codec du contrôle](../../docs/work/controle-documentaire-portable.fr.md)
restitue exactement les slots, leurs liaisons optionnelles, la file typée
restante, le contexte, le compteur et le dernier résumé. Il couvre aussi
les liaisons absentes et les sorties permises qui manquent leur but.
Les codecs de contexte `Nat` et `List Nat` sont construits ; un autre type
de contexte doit fournir son propre codec exact.

Les tests vérifient 18 reprises du contrôle et du stockage dans de nouveaux
processus et 20 refus de fichiers invalides. La file chargée contient encore
une citation et une somme dépendante. La continuation de ces tâches est
également exécutée après chargement du contrôle, avec le même dossier maître
et le même stockage encore fournis. Cette condition est explicite : le
chargement physique du maître et du présent entier reste ouvert.

```text
lake build Tests.LocalAlignment.DocumentaryPortableControlCases
python -B scripts/check-documentary-control-codegen.py
python -B scripts/run-documentary-control-smoke.py
```

## Recettes des producteurs maître

Les [sept recettes maître](../../docs/work/recettes-producteurs-maitre.fr.md)
reconstruisent les producteurs existants à partir de leurs ports et de leur
environnement dépendant. La capture conserve les valeurs déjà produites ;
les preuves restituent le support et le curseur entiers pour la classe formée,
qui couvre les traces documentaires, adaptatives et mémoire finies déclarées.

Les codes d'opération et positions de ports ont leur codec depuis des octets.
Les valeurs et environnements maître restent à encoder : ces enregistrements
ne sont pas le checkpoint maître. Le test runtime lit les ports de trois
exécutions réelles et contrôle huit encodages et douze formats invalides.

```text
lake build Tests.LocalAlignment.DocumentaryMasterFormationCases
python -B scripts/check-master-recipes-codegen.py
python -B scripts/run-master-recipes-smoke.py
```

## Assignation et lecteur mesuré depuis des octets

Le [codec de l’assignation et du lecteur](../../docs/work/assignation-lecteur-portables.fr.md)
conserve leurs fonctions entières, avec les opérations de lecture mesurées.
La capture lit les codes réellement retournés dans les têtes du support maître.
Les lois couvrent les traces finies maître, documentaires, adaptatives et mémoire
depuis un maître dont l’assignation est correctement représentée.

Trois lecteurs produits par les programmes existants reprennent dans de nouveaux
processus et retrouvent exactement leurs bits et compteurs. Quatre reprises de
formes supplémentaires et quinze formats invalides sont vérifiés. Ce composant
reste à réunir avec les autres valeurs et environnements du maître pour reprendre
le présent entier.

```text
lake build Tests.LocalAlignment.DocumentaryAssignmentCases
python -B scripts/check-assignment-codegen.py
python -B scripts/run-assignment-restart-smoke.py
```

## Assignation séquentielle avec ses invariants

Le [raccord dépendant](../../docs/work/assignation-sequentielle-portable.fr.md)
restaure maintenant le SequentialAssignment entier dans une classe de recettes
validée par un contrôle fini. Les invariants sur toutes les variables futures
sont construits à partir des bornes des retournements. La fermeture couvre
toutes les traces finies déclarées depuis un maître représenté dans cette classe.

L’assignation chargée devient le champ exécutable de l’état maître conservé.
Ce premier raccord reçoit les autres champs de cet état. Trois reprises physiques
réelles et quatre formes supplémentaires exécutent ensuite une nouvelle étape ;
21 entrées invalides sont refusées. L’encodage des autres valeurs maître,
leur représentation complète en octets et la reprise du présent entier restent à réaliser.

```text
lake build Tests.LocalAlignment.DocumentarySequentialCases
python -B scripts/check-sequential-codegen.py
python -B scripts/run-sequential-restart-smoke.py
```

## État maître et checkpoint assemblé

Le [nouveau raccord](../../docs/work/etat-maitre-et-checkpoint-assemble.fr.md)
restitue maintenant l’état transmis entier depuis les octets : assignation
avec lecteur, génération, graine de recherche, décisions ordonnées et provenance.
Les constitutions et histoires enracinées ont aussi leurs codecs exacts.
Les preuves couvrent les traces finies déclarées depuis un curseur représenté ;
le chargeur de l’état ne reçoit pas l’ancien état.

Trois reprises froides retrouvent les composants réels et exécutent une nouvelle
étape sur l’état complet chargé. Trois sources supplémentaires et 18 refus
vérifient les compteurs conservés, les décisions répétées et la validation.
Le contrôle du C inspecte 29 chemins et rejette 104 injections interdites.

Le checkpoint réunit source, stockage, mémoire et contrôle en sections d’octets
avec les autres ressources maître dans un payload typé. Il restitue exactement
le présent entier et conserve tous les futurs déclarés dans ce cadre. Après
relecture du fichier avec ce payload conservé, la citation et la somme restantes
s’achèvent au tour 5, avec une file vide.

Les découvertes, applications, décompositions et environnements historiques
du maître restent à représenter en octets. La reprise du présent entier dans
un nouveau processus depuis un fichier seul reste ouverte.

```text
lake build Tests.LocalAlignment.DocumentaryAssembledCases
python -B -X utf8 scripts/check-state-assembly-codegen.py
python -B -X utf8 scripts/run-state-assembly-smoke.py
```
