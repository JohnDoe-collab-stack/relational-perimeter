# Réouverture des revues de la correspondance runtime–réels effectifs

Date : 18 octobre 2026.

Nouvelle révision d'évidence courante :
`83e797e28b9762324e0d9e33675b9be5becf23f0`.

Ancienne révision revue conservée :
`1a2bd65b080fc9eefca60bd91dbb175a9a458862`.

## Cause exacte de la réouverture

L'empreinte conservatrice de
`RUNTIME_EFFECTIVE_CAUCHY_REAL_CORRESPONDENCE` couvre 182 fichiers. Aucun
module Lean cité par l'affirmation ni aucun de ses imports locaux n'a changé
entre les deux révisions. Les dépendances enregistrées qui ont évolué sont les
contrôles partagés suivants :

- vingt lignes ont été ajoutées à `scripts/expected-failures.tsv` ;
- huit lignes ont été ajoutées à `scripts/stratification.tsv` ;
- `scripts/verify.sh` et `scripts/verify.ps1` appellent désormais le nouveau
  contrôle compilé de la complétion de carrier.

Ces changements sont additifs et concernent les gates 7.1–7.3, mais ils
modifient des fichiers explicitement inclus dans l'empreinte de l'affirmation.
La procédure interdit donc de transférer automatiquement les revues
antérieures ou de retirer ces contrôles de la portée afin de rendre
l'empreinte verte.

## Décision de traçabilité

L'affirmation courante est rattachée au snapshot publié `83e797e...`. Les
revues de lecture et de traduction redeviennent `pending` ; l'audit indépendant
reste `not_recorded`.

La [revue de clarification historique](runtime-real-audit-clarifications-reader-translation-1a2bd65.fr.md),
la [revue antérieure sur `5e69b1b`](runtime-real-native-correction-reader-translation-5e69b1b.fr.md),
le [rapport Aristotle sur `5e69b1b`](aristotle-runtime-real-structural-audit-5e69b1b.md)
et sa [rectification](aristotle-runtime-real-structural-audit-5e69b1b-erratum.fr.md)
restent inchangés et attachés à leurs révisions respectives. Aucun de leurs
verdicts n'est transféré à `83e797e...`.

Cette réouverture ne modifie aucun module Lean, énoncé, contrat, quantification
ou passage canonique de la correspondance runtime–réels effectifs.
