# Une IA locale raccordée à l'exécuteur constitutif

Le modèle choisit des propositions. Le noyau Lean produit les réponses et les
actions autorisées sous le contrat reçu. Le contexte du modèle peut être effacé
pendant la tâche : l'exécuteur conserve sa mémoire et son contrat.

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
