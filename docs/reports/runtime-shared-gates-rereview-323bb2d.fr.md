# Relecture des affirmations partagées après la gate 7.4

Révision examinée : `323bb2d72724804dc38a93316127a1efcba3042a`.

## Portée

Cette revue rouvre et examine sur la révision ci-dessus les affirmations :

- `GODEL_RELATIONAL_SEQUENTIAL_COMPLETENESS` ;
- `RUNTIME_EFFECTIVE_CAUCHY_REAL_CORRESPONDENCE` ;
- `RUNTIME_PRESENTED_DYADIC_COMPLETION_CHARACTERIZATION`.

Elle ne transfère aucun verdict d'une révision antérieure. Elle sépare la
lecture française, la lecture anglaise, la confrontation aux déclarations et
corps Lean, et les contrôles mécaniques. Elle ne constitue pas un audit
indépendant.

## Cause exacte des empreintes rouvertes

Pour l'affirmation Gödel, la fermeture locale de ses preuves est inchangée
depuis `83e797e28b9762324e0d9e33675b9be5becf23f0`. Les seules entrées de son
empreinte modifiées sont `scripts/expected-failures.tsv` et
`scripts/stratification.tsv`, étendues pour la gate 7.4.

Pour la correspondance effective, la fermeture locale de ses preuves est
également inchangée depuis `83e797e28b9762324e0d9e33675b9be5becf23f0`.
Les seules entrées modifiées sont les deux manifestes précédents et les deux
façades `scripts/verify.sh` et `scripts/verify.ps1`, qui appellent désormais
les contrôles de la gate 7.4.

Pour la caractérisation de complétion dyadique présentée, les mêmes quatre
contrôles partagés ont changé. En outre, les lemmes génériques
`composeSignedBoundMixed`, `sixFineOneMiddleBudget`,
`DirectedUpper.align`, `DirectedUpper.composeThreeOneThree` et
`strengthenSeparationThreeLinks` ont été extraits, corps inchangés, de
`CarrierQuantitativeTransport` vers `DyadicOrderTransport`. Le module source
du symbole cité `DirectedUpper.composeThreeOneThree` est donc mis à jour dans
le registre. `CarrierQuantitativeTransport` importe cette extraction et les
théorèmes carrier continuent d'en consommer les mêmes termes.

## Lecture française autonome

Les trois passages français ont été lus sans consulter d'abord les résumés du
registre. Leur quantification et leurs limites sont cohérentes entre elles :

- la branche Gödel reçoit une famille exécutée sur le périmètre exact produit,
  réalise les futurs finis requis et rejette la fermeture du même régime sans
  produire d'approximation numérique depuis la contradiction ;
- la correspondance effective porte sur les présentations et carriers reçus,
  les opérations, relations et familles effectivement construites, sans
  reconstruction des histoires ;
- la caractérisation présentée est relative à tout contrat constructif
  explicitement réalisé et ne prétend pas encore identifier un modèle externe
  particulier des réels usuels.

Aucun passage ne transforme une projection aval en primitive constitutive.
Les distinctions occurrence/valeur, production/readout, témoin riche/code et
équivalence comportementale/égalité sont conservées.

## Lecture anglaise autonome et traduction

Les trois passages anglais ont ensuite été lus indépendamment. Ils conservent
les mêmes quantificateurs, les mêmes données reçues et les mêmes
non-conclusions. En particulier :

- « every finite future required » ne devient pas une boucle totale ;
- « closed runtime carrier » conserve l'ouverture explicite du constructeur
  `certified` relativement à son service reçu ;
- « relative characterization » ne devient ni une égalité de fonctions ni
  une identification à tous les réels classiques.

La traduction française/anglaise est validée sur cette révision.

## Confrontation constitutive aux preuves

La chaîne a été contrôlée dans l'ordre relations et témoins positifs,
occurrences et histoires, contextes, recherche, action et préservation,
autorisation, continuation, mémoire, puis observations et readouts.

| Passage | Formation | Exécution | Preuve | Transport et oubli |
| --- | --- | --- | --- | --- |
| Gödel–regroupement | La famille et le périmètre exact sont des indices reçus ; la clôture totale est un type distinct. | Les sources chronologiques produisent la charge transportée, la cible installée et sa continuation. | Le même témoin diagonal rejette `Truth(G) -> Proof(G)` et la fermeture du même régime. | La projection mémoire oublie les ressources riches seulement sous environnement et contrat de futurs fixés. |
| Correspondance effective | Présentations, carriers et familles reçoivent leurs modules et lois ; l'inverse reçoit l'apartness. | Les archives courantes produisent les actions, cibles et pas avant projection. | Les six blocs de `effectiveCorrespondence` sont remplis par les théorèmes antérieurs ; l'unicité native médie le même pas terme. | Les équivalences numériques ne récupèrent ni banques, journaux, programmes, témoins ni occurrences. |
| Complétion présentée | `complete` reçoit une famille, jamais un candidat ni un morphisme terminal. | `carrierCompletion` conserve le paquet natif produit avant `toCarrier`. | Les morphismes, retours et transports sont dérivés de la complétude et de l'unicité ; le transport d'ordre conserve ses sept bornes dirigées après l'extraction de module. | La caractérisation est comportementale et relative ; densité et bornes transportent les témoins reçus sans resélection. |

La relecture des types complets confirme que les hypothèses restent placées au
niveau annoncé. Aucun champ terminal n'a été ajouté aux interfaces et aucun
readout n'est réimporté pour constituer rétroactivement le runtime.

## Verdict

Les revues `reader` et `translation` des trois affirmations sont validées sur
la révision exacte examinée. Les extensions de contrôle et l'extraction de
module n'affaiblissent aucune conclusion enregistrée. Le statut
`independent` n'est pas évalué par ce document et doit rester distinct jusqu'à
la réception et la lecture d'un rapport extérieur visant exactement cette
révision.
