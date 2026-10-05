# Soumission de l'audit indépendant des corrections de l'agent

L'envoi a été accepté par l'API Aristotle le 5 octobre 2026. Le statut de la
tâche immédiatement après création est `QUEUED`. Aucun verdict indépendant
sur cette révision n'est disponible au moment de ce reçu.

## Révisions effectivement transmises

- Dépôt : https://github.com/JohnDoe-collab-stack/relational-perimeter.git
- Branche : `codex/constitutive-agent-corrections-audit`.
- Commit scientifique : `d52f3c0311d9572f84863481d508d38db2e5613c`.
- Parent scientifique : `924bc6c38153e6e5e7e0b2290d03b5eca28881dd`.
- Publication du prompt seulement : `cc191a74de21bdac9b56b9a11fcaa5ed9729ef2c`.
- Main et merge-base : `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685`.
- Agent précédemment audité : `f6c6d2c051ae0886056d47cf5357253c137a1319`.

Le parent reprend les corrections d'unification déjà publiées. La branche
isolée ajoute les corrections de l'agent et de ses gates ; elle n'intègre
pas les travaux parallèles sur les signatures de continuation. Ni ces
travaux ni leur répertoire n'ont été modifiés. Aucune fusion dans main n'a
été effectuée.

## Prompt et reçu API

Le [prompt complet](../../ARISTOTLE_CONSTITUTIVE_AGENT_CORRECTIONS_AUDIT_PROMPT.md)
contient 19 sections, 49 questions, les 20 familles de mutations initiales
et la revue obligatoire des corrections F1-F7. L'exigence et le critère
d'achèvement reçus sont cités sans modification. L'auditeur doit récupérer
lui-même le dépôt public et auditer le commit scientifique détaché.

Empreinte SHA-256 des octets du blob Git effectivement transmis :

```text
b0add7f7d203ec32f25f8b0c818bd3640d975edcd2a722781428801c80e81fd3
```

- SDK utilisé : `aristotlelib 2.1.0`, `Project.create(prompt=...)`.
- Projet : `a55ce7b7-a3b4-4d77-b963-812c1923c77b`.
- Tâche : `1ff3164b-33e2-4763-aa8b-425695482d7f`.
- Date de création renvoyée par l'API : `2026-10-05T11:04:22.245175`.
- Statut du projet à la création : `RUNNING`.
- Statut de la tâche lors de la lecture immédiate : `QUEUED`.

Une seule création a été exécutée, sans relance automatique. Le prompt
entier a été transmis ; aucune archive locale ni clé API n'a été publiée.
Les vérifications préalables de l'envoi contrôlent le parent, le merge-base,
la tête distante, la propreté du checkout, le diff limité au prompt et son
empreinte. Ce reçu est un ajout documentaire ultérieur, pas une nouvelle
révision scientifique à substituer au commit audité.

## Vérifications locales avant publication

Sur le répertoire isolé et le contenu ensuite commité :

- `lake clean`, puis `lake build +RelationalPerimeter` : 160 jobs, succès.
- `lake build` : 183 jobs, succès, sans avertissement Lean.
- `bash scripts/verify.sh` et `pwsh -NoProfile -File scripts/verify.ps1` :
  succès sur Windows, mêmes 181 fichiers Lean.
- Sweep : 18 224 constantes, 180 modules audités, aucune dépendance
  axiomatique manuscrite ; 360 exceptions générées signalées par le sweep.
- Matrice des wrappers : 36 cas réussis ; politique lexicale : 288 cas
  positifs, 576 refus et 288 contrôles de position.
- Client public : 14 déclarations compilées sans axiome.
- Liens locaux des documents modifiés : 99 liens résolus.
- `lake update` : manifeste inchangé ; `git diff --check` : succès.
- Empreintes avant/après : les 301 fichiers du contenu scientifique sont
  inchangés pendant la validation ; le prompt séparé n'entre pas dans ce total.
- Les quatre fichiers fondamentaux, la licence, la toolchain et les fixtures
  d'échec restent inchangés par rapport au parent et à l'agent audité.

Ces résultats sont des vérifications de l'auteur, pas le verdict indépendant.
Le protocole demande deux verdicts distincts : établissement de la cible
complète de l'agent et absence de régression des résultats antérieurs.

Ce document de chantier et les plans/protocoles temporaires devront être
retirés avant une éventuelle intégration dans main explicitement autorisée.
