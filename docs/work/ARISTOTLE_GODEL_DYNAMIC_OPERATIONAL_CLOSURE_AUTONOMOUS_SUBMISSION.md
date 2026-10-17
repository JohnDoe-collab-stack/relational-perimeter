# Reçu de soumission autonome — audit Aristotle de la fermeture opérationnelle Gödel

## Statut

Le premier projet Aristotle, qui ne disposait d'aucune source, reste un échec
de livraison sans verdict. Il n'est ni continué ni utilisé comme évidence.

Un nouveau projet a reçu les sources, l'historique Git complet et un toolchain
Linux Lean 4.33.1 autonome. La tâche d'audit intégrale a été créée après la
vérification de ces entrées. Sa mise en file d'attente n'est pas un verdict :
la revue du registre demeure `independent=not_recorded` jusqu'à réception et
lecture du rapport terminé.

## Cible immuable

- branche publiée : `work/godel-dynamic-operational-closure` ;
- base : `c3a12b5114ca519aae8e8c83eec6b6d723d450d4` ;
- code, preuves, tests et texte scientifique :
  `e2b75474c8bef91cfb9f24d6fed8d408e38d0269` ;
- révision exacte auditée, registre compris :
  `31d9d0765298acd0d1e9715b57cc8adcfcb7cd7b` ;
- affirmation : `GODEL_OPERATIONAL_RUNTIME_CLOSURE_OBSTRUCTION`.

## Entrées autonomes vérifiées

L'archive source `relational-perimeter-godel-source-31d9d07.tar.gz` contient
les sources sans objets de compilation :

- taille : `19349007` octets ;
- SHA-256 :
  `6e8c0b8e8ca6449e360519d45b6c6b11f33dce3fd54ccd287d14962818bc7627`.

Le service ayant retiré le répertoire `.git` imbriqué lors de l'extraction,
l'historique a été fourni séparément sous forme de bundle complet :

- fichier : `relational-perimeter-history-31d9d07.bundle` ;
- taille : `4920351` octets ;
- SHA-256 :
  `96747eb16bef8ce0bf196b514ab92ea66e38b371f6001c8817cd0a35764526e9`.

La tâche de restauration a confirmé : bundle complet, `HEAD` détaché à la
cible exacte, arbre propre, `git fsck` sans erreur, et ascendance des deux
révisions de base et d'évidence. Les 17 chemins exigés par le manifeste sont
présents et suivis.

Le toolchain Linux réduit a été construit exclusivement depuis l'archive
officielle Lean 4.33.1, puis testé par un build propre de la cible exacte. Son
archive reconstruite possède :

- taille : `475582109` octets ;
- SHA-256 :
  `e17865e02d7df304e195253516c9a7f7afdb3202e5a13d471a89c032c0621f86` ;
- Lean : `4.33.1`, commit
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` ;
- Lake : `5.0.0-src+819816b`.

Il a été transmis en six fragments, tous vérifiés avant l'envoi :

| Fragment | Octets | SHA-256 |
| --- | ---: | --- |
| `part-00` | 94371840 | `80800de3367d1661d6773322238c32a52eee84e18bddd2b2355741c77950123d` |
| `part-01` | 94371840 | `7b2cd62bb028c17dee0029e14a3999a038c3d892d2920931b40a72b6010842e8` |
| `part-02` | 94371840 | `e5c697cc3aae96696f2d3a1d20cedbbdcfe79dc85a37da8d8ea9331b28d0b2e2` |
| `part-03` | 94371840 | `f155c50c572da7c03040615d717aaa31293ddb1ea5436b0507e56652d9321805` |
| `part-04` | 94371840 | `09f9d66ce022863c8254df1f7ec4ff55cf855581573338977280e95909574801` |
| `part-05` | 3722909 | `fec576046c0509c7012e98bccc743303a8bd80c5524760ab004f84c582d3d64b` |

Le service annonce Lean 4.28.0 par défaut. Le prompt interdit de l'utiliser et
impose la reconstruction, la vérification et l'emploi du toolchain 4.33.1
téléversé.

## Identité API

- client : `aristotlelib==2.1.0` ;
- projet neuf : `6cdc8e7b-8a5b-412b-84c5-0d0dc9f612a6` ;
- création du projet : `2026-10-17T23:38:36.312110` ;
- tâche de restauration Git :
  `fbbdd61a-1afb-4bbe-854b-fba0a84d883d`, terminée avec
  `READY_FOR_TOOLCHAIN` ;
- tâche d'audit intégrale :
  `e0196fdf-14c7-42d4-bde9-54ebba47cff5` ;
- création de la tâche d'audit : `2026-10-17T23:48:05.973420` ;
- état à la création : `QUEUED` ;
- questions Aristotle : désactivées.

Le bootstrap initial du nouveau projet a signalé l'absence de `.git`, sans
auditer ni rendre de verdict. La restauration par bundle a corrigé ce seul
défaut d'entrée dans le même projet avant le démarrage de l'audit scientifique.

## Prompt effectivement envoyé

- chemin :
  `docs/work/ARISTOTLE_GODEL_DYNAMIC_OPERATIONAL_CLOSURE_AUDIT.md` ;
- objet Git : commit
  `a0b641cd3a5e55986b53b3ddae6a65b3228b7bcb` ;
- taille UTF-8 : `22746` octets ;
- SHA-256 :
  `a8bdc63a7bb0ef6b6ac026f81c0dfe83e378bfd8c8a5597be351e429275dac67`.

Le prompt fixe les sept critères, les cinq reconstructions adversariales, les
questions anti-raccourci, les contrôles d'axiomes, les spécialisations HA et la
validation phrase par phrase du texte français. Il demande un verdict binaire
uniquement après exécution de l'ensemble de ces contrôles.

## Condition de clôture

La revue indépendante ne peut être enregistrée qu'après :

1. achèvement de la tâche d'audit exacte ;
2. récupération et lecture du rapport complet et de ses fichiers ;
3. confirmation qu'il vise la révision `31d9d076...` ;
4. confrontation de chaque verdict aux sept critères et au texte français ;
5. enregistrement séparé du résultat réellement obtenu.
