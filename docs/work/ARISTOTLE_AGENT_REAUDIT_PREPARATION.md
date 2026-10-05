# Préparation du réaudit scientifique de l’agent

Statut : **PRÉPARÉ — NON ENVOYÉ**. Aucun nouvel audit Aristotle n’a été lancé.
L’autorisation porte uniquement sur le commit et le push des corrections et
du protocole. Elle n’autorise ni envoi, ni fusion dans `main`.

| Référence | Valeur |
| --- | --- |
| Dépôt | https://github.com/JohnDoe-collab-stack/relational-perimeter.git |
| Branche publiée | `codex/constitutive-agent-corrections-audit` |
| Commit scientifique à auditer | `f039bdf3d822441e9e8b976ea54cf0177f58cffe` |
| Arbre scientifique | `b42c25cbc03233e17e3577d0d45a9bb741bd1b15` |
| Parent immédiat | `27546b9db4aa72769772d9253050e92fcfb0974d` |
| Réaudit scientifique précédent | `d52f3c0311d9572f84863481d508d38db2e5613c` |
| Main et merge-base | `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685` |
| Toolchain inchangée | Lean 4.33.1 |
| Prompt autonome anglais | [ARISTOTLE_CONSTITUTIVE_AGENT_REAUDIT_PROMPT.md](../../ARISTOTLE_CONSTITUTIVE_AGENT_REAUDIT_PROMPT.md) |

Le prompt cite la cible reçue et son critère d’achèvement sans les modifier.
Il contient la récupération autonome sur GitHub, tous les SHA scientifiques,
20 sections et 58 questions. Il demande un réaudit de toute la chaîne,
de F1–F7, des corrections du certificat et des protections compilées/imports/
diagnostics, ainsi qu’un verdict distinct d’absence de régression. Aucune
réponse positive n’est présupposée. Aucun paramètre scientifique n’est à remplir.

Le commit du prompt et de cette préparation est distinct du commit scientifique.
Un tip de branche ultérieur limité à ces documents ne remplace pas le SHA à
auditer. Les anciens prompts et reçus d’envoi sont conservés comme références
historiques et ne décrivent pas un nouvel envoi.

## Vérifications locales déjà exécutées

La campagne locale est détaillée dans le
[plan de correction](PLAN_CORRECTIONS_AGENT_REAUDIT.fr.md), section 11.
Ce sont des résultats d’auteur, pas un nouveau verdict indépendant :

- Clean build public et complet : 160 puis 183 jobs, sans avertissement Lean.
- `verify.sh` et `verify.ps1` : succès, Bash et PowerShell 7 sur Windows,
  mêmes 181 sources Lean ; 159 modules et 290 dépendances locales.
- 26 fixtures à 28 sites ; 23 fixtures historiques byte-identiques.
- Suite cross-shell : 68 résultats conformes sur 34 scénarios par route,
  avec copies physiques indépendantes ; matrice des diagnostics 288 positifs
  et 576 négatifs.
- Probes clients rejoués : 66 déclarations positives sans axiomes et 15 clients
  négatifs rejetés pour leur raison attendue.
- Sweep : 18 255 constantes, 360 exceptions générées, aucune déclaration
  manuscrite dépendante d’un axiome ; origine de trois classements ambigus
  vérifiée sans réécriture du journal brut.
- Rejeu de mutations : 55 entrées, 49 rejets, quatre cas inoffensifs acceptés,
  deux anciens patches non applicables remplacés par deux adaptations exécutées.
  Aucun timeout n’est compté comme rejet scientifique.
- Aucun fichier Lean ni déclaration supprimé ; `Followed.cons` est explicitement
  renforcé et six accords fermés sont ajoutés au certificat.
- Fondations, licence, toolchain, manifeste, figures et anciens fichiers
  scientifiques protégés inchangés ; liens locaux et contrôles de diff valides.

Les contrôles compilés restent bornés ; ils ne prouvent ni complexité générale,
ni taille physique du tas, ni sécurité de tout Lean. La campagne locale ne
revendique pas de run Linux. L’auditeur devra produire ses propres preuves,
mesures de couverture, mutations et journaux sur le SHA exact.

Les documents de chantier de cette branche devront être retirés lors d’une
éventuelle PR/MR d’intégration. La fusion et l’envoi de l’audit exigent des
demandes distinctes ; aucune de ces étapes n’est effectuée ici.
