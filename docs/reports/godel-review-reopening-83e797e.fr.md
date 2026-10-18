# Réouverture des revues du raccord Gödel–regroupement–réels

Date : 18 octobre 2026.

Nouvelle révision d'évidence courante :
`83e797e28b9762324e0d9e33675b9be5becf23f0`.

Ancienne révision auditée conservée :
`5e69b1bae964bd2aa2de0a6c53a2cebea959f6fc`.

## Cause exacte de la réouverture

L'empreinte conservatrice de
`GODEL_RELATIONAL_SEQUENTIAL_COMPLETENESS` couvre 130 fichiers : les imports
locaux transitifs de ses déclarations, les trois fichiers de configuration et
les deux contrôles explicitement enregistrés
`scripts/expected-failures.tsv` et `scripts/stratification.tsv`.

Entre l'ancienne révision et la nouvelle, aucun module Lean de preuve cité par
l'affirmation ni aucun de ses imports locaux n'a changé. Les seules dépendances
de son empreinte qui ont évolué sont les deux contrôles partagés : vingt lignes
de fixtures négatives et huit lignes de stratification ont été ajoutées pour
les nouveaux modules de complétion dyadique présentée. Les anciennes lignes ne
furent ni retirées ni modifiées.

Cette évolution reste toutefois une modification de dépendances enregistrées.
La procédure scientifique impose donc de rouvrir l'évidence ; le caractère
additif et extérieur aux modules Gödel ne permet pas de recopier l'ancienne
empreinte, de retirer les contrôles de la portée ou de transférer les statuts
de revue.

## Décision de traçabilité

L'affirmation courante est rattachée à la révision publiée `83e797e...` avec
l'empreinte source recalculée sur ce snapshot. Ses statuts redeviennent
`reader=pending`, `translation=pending` et `independent=not_recorded`.

Le [rapport indépendant historique](aristotle-runtime-real-structural-audit-5e69b1b.md),
sa [note de rectification](aristotle-runtime-real-structural-audit-5e69b1b-erratum.fr.md)
et la [revue de lecture et de traduction](runtime-real-native-correction-reader-translation-5e69b1b.fr.md)
restent inchangés et attachés exclusivement à `5e69b1b...`. Leur verdict n'est
ni annulé ni transféré à la nouvelle révision.

Cette réouverture ne modifie aucun énoncé, corps de preuve, contrat,
quantification, passage canonique ou conclusion Gödel. Elle corrige uniquement
la relation entre l'affirmation courante, son snapshot et ses revues.
