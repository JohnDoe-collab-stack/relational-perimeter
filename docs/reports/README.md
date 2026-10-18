# Rapports scientifiques

## Audit indépendant Gödel du commit `a020dc3`

[Rapport indépendant sur l’obstruction gödelienne interne](aristotle-godel-a020dc3.md),
réalisé par Aristotle (Harmonic) le 15 octobre 2026, sur le commit exact
`a020dc3267c0670b1316b2b2f8d5b3259ab40d91`.

Verdict principal : `EXACT FORMAL TARGET ESTABLISHED`. Le rapport établit la
cible dans sa portée conditionnelle enregistrée. Ses qualifications G-1 à G-9
en précisent les limites sans identifier d’obligation non satisfaite.

Deux distinctions doivent être conservées lors de la lecture :

- la chaîne terminale dépend de l’admission dans le terme de preuve, tandis
  que l’effacement des preuves peut supprimer cette lecture dans le code
  exécuté ;
- l’ordre constitutif démontré est un ordre de dépendance et de co-rétention
  des ressources, non l’affirmation que les certificats du tout et de la
  continuation sont directement consommés par le rejet terminal.

## Revues documentaires Gödel du commit `a020dc3`

La [revue autonome de lecture et de traduction](godel-reader-translation-a020dc3.fr.md)
confronte les deux passages canoniques français aux énoncés et corps Lean
complets. La lecture est validée. La traduction est déclarée non applicable,
car aucune version anglaise n'est enregistrée pour cette revendication et la
procédure interdit d'en inventer une pour fermer une case du registre.

## Rapport historique

[Audit indépendant du commit `1ca8e89`](aristotle-1ca8e89.fr.md) : rapport
conservé sans modification. Il conclut à des corrections requises pour la
révision qu'il examine, et non pour l'état actuel du dépôt.

Les protocoles, résultats bruts, journaux et mutations de ce chantier restent
consultables dans l'[arbre historique publié](https://github.com/JohnDoe-collab-stack/relational-perimeter/tree/81f67adfaa239e1af606c82233ca91ce314dab95/audit).
Ils ont été retirés de l'arbre destiné à `main`, pas réécrits. Une archive
externe avec empreintes conserve également leurs octets d'origine.

Un rapport historique n'est pas transférable à une nouvelle révision. Les
revues ouvertes du registre scientifique restent ouvertes.

## Audit historique runtime–réels du commit `5e69b1b`

L'[audit structurel indépendant](aristotle-runtime-real-structural-audit-5e69b1b.md)
et sa [rectification factuelle](aristotle-runtime-real-structural-audit-5e69b1b-erratum.fr.md)
restent attachés exclusivement au commit
`5e69b1bae964bd2aa2de0a6c53a2cebea959f6fc`.

La [note de réouverture](godel-review-reopening-83e797e.fr.md) établit que les
modules de preuve Gödel et leurs imports locaux sont inchangés, mais que deux
manifestes de contrôle partagés ont reçu des ajouts pour les lots ultérieurs.
L'affirmation courante est donc rattachée à `83e797e...` avec ses revues
rouvertes ; l'audit historique est conservé, sans transfert de verdict.

La [note de réouverture de la correspondance effective](runtime-effective-review-reopening-83e797e.fr.md)
consigne séparément les quatre contrôles partagés modifiés depuis `1a2bd65...`.
Ses anciennes revues restent historiques ; les revues courantes sont rouvertes
sur `83e797e...`.
