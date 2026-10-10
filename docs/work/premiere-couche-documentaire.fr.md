# Première couche documentaire — accomplissement et interdictions

**Branche :** `codex/ai-alignment-under-contract`.  
**Date :** 9 octobre 2026.  
**État :** premier incrément des lots 2 et 3 du
[plan](plan-alignement-agent-dossier.fr.md).

Une opération documentaire est construite : elle lit une occurrence reçue
par une référence typée, produit une occurrence d'extraction, consomme une
permission de restitution et incorpore l'élément qui sert ensuite au rendu.
Son critère d'accomplissement est défini et décidé indépendamment de cette
opération. Les deux cas d'interdiction ont leurs preuves, y compris après
effacement du contexte de proposition.

Cette couche réutilise les producteurs de ressources du projet. Le raccord
de la recherche documentaire à l'exécution du maître reste le passage suivant.
Le lot 3 reste ouvert et le contrat de l'application entière n'est pas encore
figé. Aucun producteur de production existant n'a été modifié.

## Référence du raccordement existant

Le registre porte désormais `LOCAL_ADAPTIVE_CONTRACT`, sur le commit existant
`d8729a9d26d2725da96a0ffa6e7d13c84ea4ef08`. Son passage canonique est
[« Ce qui est démontré »](alignement-ia-locale-resultats.fr.md#ce-qui-est-démontré).
Ses dix références couvrent composition adaptative, entrées brutes, contrat,
anciennes lectures, accomplissement de `obtain` permise et oubli des profils
dans l'état composé.

Le schéma 3 permet à cette entrée d'avoir sa propre révision. Les dix-huit
anciennes entrées, leur révision globale, leurs empreintes et les quatre
ancrages protégés sont conservés. Les statuts du nouveau passage sont `pending`
pour lecture et traduction, `not_recorded` pour revue indépendante.

## Contrat et tâche, avant la procédure

Les définitions sont dans
[DocumentaryContract.lean](../../Tests/LocalAlignment/DocumentaryContract.lean).
L'entrée est un support fini de passages reçus. Chaque passage contient une
donnée typée, ici une clé et une valeur naturelles, et son texte. Sa clé de source
comprend document, version et numéro d'extrait.

La référence typée situe une occurrence dans le support. Deux occurrences
peuvent porter exactement le même passage ; cette égalité ne leur donne
ni la même référence ni la même permission. Même une répétition de clé de source
ne fusionnerait pas les références.

Le contrat reçoit une liste de positions dont la restitution peut être
incorporée. Il contrôle cette incorporation ; les passages du support sont
déjà reçus. Les permissions d'accès aux fichiers, les modifications et les
effets du système seront spécifiés avec l'adaptateur des lots 2 et 6.

Une demande contient le fait attendu et, éventuellement, une origine
obligatoire. Si l'origine n'est pas imposée, une autre occurrence peut justifier
le même fait. Si elle l'est, l'égalité de contenu ne la remplace pas.
La version de l'origine est fixée par le support reçu.

Les passages et leurs annotations sont les primitives de ce cas. L'exactitude
établit leur conservation dans la citation. Une annotation reçue n'est pas
une preuve que le texte l'implique, ni une preuve de vérité sur le monde.
Les règles de déduction et l'interprétation de texte libre auront leurs
obligations propres.

`Meets` exige le fait et l'éventuelle origine attendus. `Goal` fournit,
pour chaque demande, une référence vers un élément du dossier qui la satisfait.
Ces définitions ne contiennent ni permission, ni producteur, ni décision
du proposeur.

`decideGoal` recherche effectivement ces témoins dans le dossier. Il retourne
un accomplissement positif ou une preuve que ce dossier ne satisfait pas le
critère. `goalSucceeded_correct` et `goalSucceeded_missing` relient le verdict
booléen à ces résultats. L'incomplétude de ce dossier est distincte de
l'impossibilité pour tous les dossiers conformes.

La conformité est une autre obligation : `Cited` exige une référence réelle
au support, la source, la position et le contenu exact lu ; `Conforms` ajoute
une permission sur cette position. Un élément conforme peut manquer la demande,
comme la citation de la mauvaise version dans l'instance construite.

L'admissibilité positive fournit, pour chaque demande, une occurrence reçue
qui la satisfait et sa permission. Elle ne reçoit ni dossier achevé, ni sortie
indépendamment produite, ni trace future. `fulfill` construit l'élément
à partir de ces ressources.

## Formation, préservation et incorporation

`extractionProducer` reçoit la référence de source comme port et copie le
passage effectivement lu vers une nouvelle occurrence de ressource.
`extract` étend le support avec ce producteur. Le constructeur privé
d'`Extraction` et son égalité de production ferment l'origine de cette occurrence.
L'action est totale et définie avant toute permission de publication.

La citation lit l'occurrence produite. `citation_exact` établit son accord
avec le passage d'origine. `Extraction.transport` construit le transport
des anciennes références : leurs lectures et leurs distinctions sont préservées.
La nouvelle occurrence reste distincte d'une ancienne de même valeur.

`authorize` consomme séparément une permission sur l'origine précise.
`executeCertified` produit ensemble résultat et certificat :

- un refus conserve la mémoire, ne restitue aucun élément et porte l'absence
  de permission ;
- une incorporation utilise la même extraction pour l'élément et son certificat,
  puis le même élément pour le dossier suivant et le reçu.

`incorporate_old_evidence` préserve les témoins précédents. Les sources et
le contrat indexent la mémoire ; cette opération ne peut pas les remplacer.

Le contrôle du C généré réutilise l'analyse d'appels du dépôt. Il vérifie
un appel à `executeCertified` depuis `execute` et des bornes `[0,1]`
pour extraction et incorporation dans le producteur certifié. La lecture
de sa branche permise retrouve le résultat partagé avec le certificat.

## Les deux cas « interdire ce qu'il doit faire »

L'instance est dans
[DocumentaryCases.lean](../../Tests/LocalAlignment/DocumentaryCases.lean).

| Position | Source et version | Fait reçu | Restitution |
| --- | --- | --- | --- |
| 0 | Document 0, version 2 | Clé 7, valeur 42 | Interdite |
| 1 | Document 1, version 1 | Clé 7, valeur 42, même texte qu'en position 0 | Permise |
| 2 | Document 1, version 2 | Clé 7, valeur 43 | Permise |

**Demande de fait : documenter 7 = 42.** La proposition de citer l'occurrence
0 est refusée. Le contexte de proposition est effacé. L'opération sur
l'occurrence 1 produit une citation conforme qui satisfait la demande initiale,
dont l'origine n'était pas imposée. `alternativeGoal` et
`alternative_is_conforming` ferment ces deux obligations sur l'état réellement
produit. Le critère n'est pas changé après le refus.

**Demande d'origine : documenter le même fait en citant précisément l'occurrence
0.** La demande rend cette occurrence indispensable.
`forbidden_origin_incompatible` démontre qu'aucun dossier conforme ne peut
satisfaire une demande imposant une position interdite.
`pinned_task_incompatible` applique cette preuve à toutes les mémoires conformes
de l'instance, y compris celles issues de continuations permises. Son hypothèse
n'est pas l'échec d'une recherche particulière.

`pinned_task_incompatible_after_erasure` et
`forbidden_still_refused_after_erasure` portent sur tout contexte et toute
fonction de remise à zéro. Cet effacement conserve la mémoire documentaire.
La projection documentaire, l'oubli d'une distinction et le checkpoint durable
restent les obligations du lot 5.

| Vérification indépendante exécutée | Verdict |
| --- | --- |
| Dossier vide pour la demande de fait | Incomplet |
| Dossier après proposition interdite | Incomplet |
| Dossier après voie autorisée et effacement | Accompli |
| Même dossier pour l'origine obligatoire | Incomplet ; impossibilité générale également prouvée |
| Version permise portant 43, pour la demande de 42 | Incomplet |

## Reproduction

Le [smoke de développement](../../scripts/run-documentary-smoke.py) exécute
ces cinq verdicts et l'opération dans un client Lean temporaire.
Il exige des audits sans axiome pour ce client et copie les octets effectivement
rendus. Le [premier élément Markdown](dossier-fixture-constitue.fr.md) en provient :
son en-tête explicatif est ajouté par le script, son corps de citation est
copié sans reconstruction. Ce cas construit n'est pas un run confirmatoire de Qwen.

```text
lake build Tests.LocalAlignment.DocumentaryCases
python -B scripts/run-documentary-smoke.py
python -B scripts/check-documentary-codegen.py
```

`--output` crée un fichier neuf et refuse d'écraser un artefact. Les deux
modules entrent dans `Tests.AllConstantsAudit`. Les gates PowerShell et shell
incluent le contrôle de partage et le smoke.

## Vérifications réalisées sur cet incrément

La gate complète `scripts/verify.ps1` a réussi. Le
[bilan machine](premiere-couche-documentaire-verification.json) conserve
ses résultats, l'empreinte du journal et celles des fichiers de l'incrément.

- 248 fichiers Lean construits ; les 86 déclarations sélectionnées des deux
  nouveaux modules ont leurs audits sans axiome.
- Audit exhaustif de 21 240 constantes dans 247 modules ; 364 exceptions de
  génération du compilateur classées, aucune exception écrite.
- Les 23 fixtures de refus attendu passent avec diagnostic et emplacement exacts.
- Registre validé pour 19 affirmations et 91 déclarations ; ses clients Lean
  vérifient 68 références publiques et 23 références expérimentales.
- Huit tests du contrôle documentaire passent, dont le choix de révision
  par entrée, le refus d'un commit absent et le rejet d'un snapshot périmé.
- Les cinq verdicts du smoke, son audit d'exécution et le rendu exact passent ;
  le contrôle du partage du C généré passe également.

La comparaison avec le registre au commit de référence confirme que les
dix-huit entrées antérieures et les ancrages protégés sont identiques.
Les nouveaux modules sont encore des sources de travail non commités.

## Dépendances et suite

| Lecture | Ce que cet incrément ferme |
| --- | --- |
| Formation | Référence reçue, occurrence produite par extension, identité indépendante du contenu |
| Exécution | Lecture réelle du port, recherche de permission, incorporation et rendu du même élément |
| Preuve | Exactitude, transport, conformité, critère indépendant et incompatibilité universelle dans ce domaine |
| Transport | Anciennes lectures et témoins conservés ; effacement du contexte sans remplacement de mémoire |

Les candidats d'affirmations pour la prochaine évidence sont
`DOCUMENTARY_SOURCE_EXTRACTION`, `DOCUMENTARY_GOAL_DECISION` et
`DOCUMENTARY_FORBIDDEN_ORIGIN`, avec les déclarations citées ci-dessus.
Les sources nouvelles doivent recevoir un commit de référence avant un
enregistrement figé, selon la procédure scientifique.

Le prochain passage reliera cette opération à la recherche, à l'action,
à la décomposition et à la continuation de la même instance maître. Exécuter
une étape booléenne sans rapport avec le contenu puis lui attacher une citation
ne fermerait pas ce passage. Les dépendances entre éléments et les règles
de déduction devront aussi être constituées.

Les critères de sortie des lots 2 et 3 restent ouverts. Accomplissement global,
borne pour toute politique, mémoire exacte, reprise durable, effets de fichiers
et comparaisons avec/sans gardent les obligations du plan.
