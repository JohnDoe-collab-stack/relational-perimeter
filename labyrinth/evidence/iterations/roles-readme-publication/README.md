# Labyrinth des fondations

Application locale de la méthode [Labyrinth exploration](https://github.com/nasqret/labyrinth-exploration) aux fondations de Relational Perimeter. La carte décrit les sources relues pour la livraison de `codex/positive-circular-foundations`, depuis la base `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685`. Le snapshot conserve le contexte de revue dans l’arbre de travail avant commit. La première carte sur `main` est conservée dans [l’archive](evidence/iterations/main-8a5e494/knowledge.json).

Lire [la carte en français](FONDATIONS.fr.md), puis ouvrir [le tableau de bord](dashboard/index.html#sota). Les sources Lean existantes restent les preuves canoniques ; `knowledge.json` et `sota.json` sont les données canoniques de cette carte. Les documents et le tableau de bord sont régénérés.

## Périmètre

- `SegmentedResidualRole.lean` : noyau de détermination résiduelle et reconstruction interne.
- `AbstractSegmentedTurning.lean` : frontière, régime, diagnostic et tournant couplé.
- `ExactTypeTransport.lean` : deux applications et leurs lois de retour.
- `StrongPerimetralTurning.lean` : instance circulaire, histoires, interprétation et modèles séparateurs.
- `RelationalPerimeter/Constitution/` : données positives, formation et histoires composables, déploiement, pont historique exact, frontière avant choix, transports complets et classification relative des rôles équipés.
- `RelationalPerimeter.lean` : façade publique, examinée sans inclure le chantier computationnel dans les conclusions.
- Documents explicatifs français/anglais et plan local de reconstruction : portée et questions proposées.

Le plan historique est conservé comme référence : ses interfaces générales restent des propositions, tandis que les réalisations disposent de déclarations et de preuves précises dans la carte. Les 47 fichiers couverts et leurs empreintes sont consignés dans [le snapshot actif du lot 4](evidence/roles-source-snapshot.json). Les snapshots [initial](evidence/source-snapshot.json), [positif](evidence/positive-source-snapshot.json), [du lot 1](evidence/closing-source-snapshot.json), [du lot 2](evidence/generation-source-snapshot.json) et [du lot 3](evidence/transport-source-snapshot.json) restent intacts. Leurs cartes et captures sont conservées dans `evidence/iterations/`, dont [signature-transport-lot3](evidence/iterations/signature-transport-lot3/knowledge.json).

Les sondes de recherche sont archivées en `.lean.in`, directement exécutables par `lake env lean`. Ce suffixe permet de les conserver hors des modules de production et de la recherche globale de fichiers `*.lean` faite par `scripts/verify.ps1`, qui attend un fichier compilé pour chaque module. Le rapport de relecture et les premiers événements conservent leurs noms `.lean` historiques ; [le registre d’archivage](PROBES.fr.md) donne les chemins actuels et les empreintes.

## Reproduire

Python 3.9+ et le toolchain Lean fixé par `lean-toolchain` sont requis. Sous Windows, `-X utf8` assure la lecture des accents avec le moteur original.

```powershell
./labyrinth/rebuild.ps1 -Python 'CHEMIN_VERS_PYTHON3' -VerifyLean
```

Sans `-VerifyLean`, le script contrôle les sources, vérifie les métadonnées et reconstruit seulement les livrables. Sur cette machine, l’alias Windows `python` ne pointe pas vers un interpréteur installé ; la première exécution a utilisé le Python fourni par le runtime Codex, découvert via `load_workspace_dependencies`.

Pour modifier la carte après une nouvelle révision : archiver le snapshot et les journaux précédents, actualiser les références et les énoncés, refaire les vérifications puis obtenir une relecture indépendante. Les états de revue ne sont pas reconduits automatiquement.

Pour la livraison autorisée de sources inchangées, le snapshot du lot 4 normalise uniquement CRLF vers LF, comme le stockage Git. Sa base et son contexte de revue sont conservés ; une révision descendante sur la même branche est admise seulement si toutes les empreintes restent identiques. Cette politique explicite ne valide aucun changement de preuve. `snapshot.py --verify-tree HEAD` vérifie aussi que les sources réellement committées correspondent au snapshot. Les snapshots historiques gardent leur format brut original.

## Niveaux et limites

Les résultats formels restent **T2**, même après revue IA ; une vérification humaine est en attente. Compilation Lean, adéquation scientifique des énoncés et validation des métadonnées sont trois contrôles distincts. `check_foundations.py` contrôle les références et la provenance ; il ne vérifie pas le sens des preuves.

Les liens du graphe sont sélectionnés et relus. Ils ne sont ni un graphe automatiquement extrait des termes de preuve, ni une démonstration que chaque hypothèse est indispensable dans toute preuve possible.

Les résultats ci-présents n’établissent pas d’équivalence avec une autre fondation logique, ni une propriété universelle de chemins libres. Les propositions correspondantes restent des questions ou pistes T6 explicites. Aucun domaine fini taille × invariant n’est encore défini : aucun pourcentage de recherche résolue n’est fabriqué.

## Provenance de la méthode

Le moteur `lab.py` et le template HTML proviennent du dépôt amont au commit `019a93da59313e697dc6f28bcfe1588a376c7565`, sous licence MIT conservée dans `UPSTREAM_LICENSE`. Le paquet complet a été lu dans un répertoire temporaire ; aucune installation personnelle de skill n’a été effectuée. Le template est adapté aux fondations : accueil sur l’état des résultats, onglets de frontière masqués en l’absence d’atlas, navigation partiellement française et hypothèses/preuves consommées visibles dans les fiches du graphe. Le moteur Python original reste inchangé.

Le tableau de bord reste local. D3 et les fontes du template chargent des ressources depuis leurs CDN ; le graphe nécessite cet accès réseau. Le rapport Markdown reste lisible sans ces ressources. Aucune publication ou synchronisation distante n’est effectuée.

La première relecture est dans [referee-foundations](../research/agents/referee-foundations/report.md). L’extension positive a sa [relecture](../research/agents/referee-positive-foundations/report.md), le lot 1 son [archive](../research/agents/referee-closing-boundary/report.md), le lot 2 sa [revue](../research/agents/referee-positive-generation/report.md), le lot 3 sa [revue](../research/agents/referee-signature-transport/report.md), et le lot 4 sa [revue indépendante](../research/agents/referee-circular-roles/report.md) avec ses propres sondes. Les brouillons de [formation](../research/agents/author-formation-transport/report.md) et de [transport des rôles](../research/agents/author-circular-role-transport/report.md) gardent leurs rapports d’auteur distincts. Le [journal](JOURNAL.fr.md) conserve les six sessions. La construction complète et `scripts/verify.ps1` ont réussi ; la portée couverte reste celle explicitée dans les énoncés.
