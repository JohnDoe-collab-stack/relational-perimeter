# Raccord documentaire à la recherche du maître

**Date :** 9 octobre 2026. **Branche :** `codex/ai-alignment-under-contract`.
Cet incrément de développement poursuit les lots 2 et 3 du
[plan](plan-alignement-agent-dossier.fr.md). Les sources sont encore non
commitées ; le [bilan de vérification](raccord-documentaire-maitre-verification.json)
en conserve les empreintes et la révision de départ.

## Résultat établi

Un premier raccord sémantique est construit et prouvé pour une demande de fait
et deux occurrences sources reçues. La demande garde son critère indépendant.
Une seule production du maître fournit la variable réellement découverte et
son successeur. Les lectures documentaires et leurs permissions déterminent
la formule reçue ; l'ouverture, la recherche de relations et le regroupement
existants produisent le routage. L'occurrence extraite est choisie en lisant
la continuation effectivement transportée. Son passage fournit le dossier,
la réponse et le Markdown rendu.

La garantie générale porte sur cette opération, pour des sources, une demande,
un contrat, deux références et une mémoire conformes quelconques :
chaque élément retourné possède sa source reçue, sa permission propre et le
fait demandé. Dès qu'une des deux sources est éligible, la décision exécutée
produit un dossier satisfaisant cette demande. Une absence de voie éligible
porte une réfutation séparée pour chacune des deux sources.

Les deux cas d'interdiction gardent leurs verdicts après effacement du contexte :
le fait demandé peut être obtenu par une autre occurrence permise ; une demande
qui impose l'origine interdite reste incompatible avec tout dossier conforme.
Cette incompatibilité universelle est le théorème de la première couche,
réutilisé avec le même contrat ; le nouveau décideur restitue effectivement
l'absence d'élément pour ce cas.

## Données reçues et sens de l'encodage

Le [module de sélection](../../Tests/LocalAlignment/DocumentarySelection.lean)
consomme des références typées aux sources de la
[première couche](premiere-couche-documentaire.fr.md).
`check` lit le passage référencé, recherche sa permission dans le contrat
reçu et applique `meetsDecision`. Son résultat contient soit la permission
positive et l'accord avec la demande, soit leur réfutation. L'autorisation
porte ici sur l'incorporation et la restitution des sources déjà reçues.

Le fait contrôlé est constitué des champs typés `key` et `value` reçus.
Le texte original est lu et restitué depuis la même source. La correspondance
entre une phrase libre et ces champs demande ses règles de validation propres,
à construire avec les déductions de la classe documentaire.

L'admissibilité du choix signifie qu'au moins une référence fournit un
passage qui répond à la demande et dispose de sa permission. Elle fournit
des ressources primitives ; le dossier est produit ensuite.

Pour la variable découverte `v`, le bit faux désigne la source gauche
et le bit vrai la source droite. La formule décrit exactement les choix :

| Gauche éligible | Droite éligible | Formule reçue | Choix satisfaisants |
| --- | --- | --- | --- |
| Oui | Oui | Aucune clause | Les deux |
| Non | Oui | Une clause contenant `v` | Droite |
| Oui | Non | Une clause contenant la négation de `v` | Gauche |
| Non | Non | Une clause vide | Aucun |

`choiceFormula_exact` prouve, pour toute affectation, que la satisfaction
de cette formule équivaut à l'éligibilité de la source désignée par son bit
en `v`. La valeur du bit garde ainsi une interprétation documentaire
exacte. L'identité de source est sa référence reçue ; l'égalité du contenu
ne remplace aucune permission.

`generated_root_accept` rétablit la satisfaction de la formule reçue
à partir de l'acceptation d'un contexte généré. Il consomme l'histoire de
formation et les décisions réalisées. `frontier_root_accept` ferme cette
loi pour la continuation réellement située dans le front retenu.
L'interprétation documentaire vaut donc aussi après son transport.

## Chaîne effectivement exécutée

Le [raccord au maître](../../Tests/LocalAlignment/DocumentaryMaster.lean)
enchaîne les constructions suivantes :

1. `search` appelle une fois `VariableMaster.masterHead`. Ses producteurs
   existants découvrent, appliquent, décomposent et constituent le successeur.
2. Les deux `check` consomment les sources, la demande et le contrat.
   `choiceFormula` utilise leurs résultats et la variable lue dans cette tête.
3. `VariableMaster.openFrontier` constitue les deux enfants depuis la racine.
   `normalizeGeneratedStructuralFrontierByFlip` recherche les relations
   entre les contextes produits et fournit son code de regroupement.
4. `Stage.preservation` compose l'ouverture et la réduction, avec leurs
   transports et leurs préservations d'acceptation. `seed` fournit une
   affectation primitive satisfaisante lorsqu'une voie existe.
5. `decide` exécute le transport avant toute extraction.
   `Stage.candidate` lit le bit de cette continuation retenue et récupère
   la permission propre à la source ainsi choisie.
6. `complete` extrait effectivement ce passage, l'autorise et l'incorpore.
   Le paquet `Completion` conserve cette continuation, cette action,
   cet élément et ce résultat, avec leurs équations d'accord.
7. `Decision.result` restitue le même élément. Le rendu utilise ses octets.
   La prochaine opération reçoit `Stage.next`, lu dans la même tête.

La découverte canonique du maître fournit la variable et sa continuation.
La partie documentaire détermine le problème reçu par l'ouverture et la
normalisation SAT. Les passages reçus interviennent donc réellement dans
cette recherche et dans le choix de l'action documentaire. Les producteurs
canoniques restent ceux de l'instance existante.

Les actions de transport agissent sur les continuations structurelles ;
leurs preuves préservent séparément l'acceptation. L'autorisation documentaire
consomme ensuite la permission de l'origine retenue. Un regroupement entre
branches ne confère pas une permission à une source interdite.

## Lois générales fermées

Les paramètres de ces lois sont les données reçues de l'opération binaire ;
ils ne contiennent ni dossier terminé ni résultat attendu.

| Déclaration | Garantie |
| --- | --- |
| `Selection.choiceFormula_exact` | Satisfaction SAT si et seulement si la source choisie est éligible |
| `Selection.Checked.complete` | Toute permission et tout accord positifs sont reconnus par le contrôle |
| `Selection.frontier_root_accept` | L'acceptation du front généré rétablit le sens de la formule reçue |
| `Master.decide_goal` | Toute paire avec une source éligible satisfait la demande dans le résultat réellement produit |
| `Master.Decision.actual_output_conforms` | Tout élément retourné est référencé et permis |
| `Master.Decision.actual_output_meets` | Tout élément retourné répond à la demande reçue |
| `Master.Completion.actual_item` | Réponse et passage de l'action effectivement produite sont le même élément |
| `Master.Completion.actual_origin` | La réponse garde la position de la source sélectionnée |
| `Master.Completion.items_exact` | L'incorporation ajoute exactement cet élément aux anciennes occurrences |
| `Master.Completion.old_source_read` | Les anciennes lectures sont conservées par l'extension réellement produite |
| `Master.Stage.next_exact` | Le point de continuation est celui de la tête effectivement exécutée |

## Instances concrètes et verdicts

Les [cas Lean](../../Tests/LocalAlignment/DocumentaryMasterCases.lean)
emploient l'origine publique existante. Les sources gardent leurs versions
et références. Les instances qui changent le contrat ou la demande sont des
cas distincts annoncés explicitement, avec leur critère propre.

| Cas construit | Résultat de la recherche et de l'exécution |
| --- | --- |
| Même fait 42 à gauche interdite et à droite permise | Front retenu de largeur 2 ; incorporation de l'occurrence droite, position 1 ; tâche accomplie |
| Même fait 42, avec les deux occurrences permises | Front retenu de largeur 1 ; transport vers l'occurrence droite ; tâche accomplie, origines toujours distinctes |
| Demande imposant précisément l'origine interdite | Aucune incorporation ; tâche inaccomplie ; incompatibilité universelle avec le contrat |
| Demande du fait révisé 43 | Occurrence position 2, version 2 ; tâche accomplie pour 43, inaccomplie pour 42 |
| Effacement du contexte de proposition | Même exécution et même verdict, pour la voie permise et la demande incompatible |
| Opération suivante depuis le successeur produit | Tâche toujours satisfaite ; première occurrence conservée ; nouvelle tête au niveau suivant |

La largeur 2 du premier cas vient du résultat de la recherche de relations ;
elle inclut une branche insatisfaisante. Ce normaliseur regroupe les branches
licenciées par ses relations et ne fait pas ici un élagage général SAT.
La largeur 1 du second cas est une lecture du front effectivement constitué.

Le [Markdown produit](dossier-fixture-maitre.fr.md) contient le passage
retourné par cette exécution. Le
[smoke](../../scripts/run-documentary-master-smoke.py) confronte
17 verdicts et lectures, vérifie les audits du client et compare les octets
effectivement rendus au cas de référence. Il crée un artefact neuf avec
`--output` et refuse tout écrasement.

## Vérification du partage et reproduction

Le [contrôle du C généré](../../scripts/check-documentary-master-codegen.py)
suit les helpers depuis `Master.run` : une tête maître, deux contrôles de
sources et une entrée dans l'ouverture et la normalisation. Depuis
`Master.complete`, il établit une extraction et une incorporation, dont
le paquet partage les résultats.

Ces décomptes couvrent leurs points d'entrée. Le transport fonctionnel entre
la recherche et l'extraction est vérifié par les lois Lean et les exécutions
du smoke ; il reste hors du décompte global de cet analyseur C.
La récursion interne du normaliseur et le coût physique ont leurs métriques propres.

```text
lake build Tests.LocalAlignment.DocumentaryMasterCases
python -B scripts/check-documentary-master-codegen.py
python -B scripts/run-documentary-master-smoke.py
```

Les trois modules nouveaux entrent dans l'audit exhaustif par
`Tests.AllConstantsAudit`. Les gates PowerShell et shell comprennent les deux
nouveaux contrôles. Le bilan lié en tête donne les résultats de la gate complète.

La gate complète `scripts/verify.ps1` a réussi : 251 fichiers Lean construits,
21 446 constantes examinées dans 250 modules, 364 exceptions du compilateur
classées et aucune exception écrite. Les 62 audits sélectionnés des trois
nouveaux modules sont sans axiome. Les 17 contrôles du nouveau smoke,
les contrôles du partage, les huit tests documentaires et les 23 fixtures
de refus attendu passent. Le registre conserve ses 19 entrées et 91 références ;
les nouvelles affirmations attendent leur propre commit d'évidence.

## Quatre dépendances et obligations suivantes

| Lecture | Dépendance réellement fermée |
| --- | --- |
| Formation | Sources et références reçues ; tête maître exécutée ; contextes engendrés ; occurrence extraite par extension |
| Exécution | Résultats des contrôles lus par la formule ; variable lue dans la tête ; code de réduction exécuté ; bit retenu lu par la sélection ; passage réellement extrait |
| Preuve | Loi sémantique ; préservation de l'ouverture et du regroupement ; permission de l'origine retenue ; accomplissement dans le dossier produit |
| Transport | Satisfaction réfléchie vers la racine ; identités sources et anciennes lectures conservées ; contexte effacé ; prochaine tête depuis le successeur produit |

Les candidats d'affirmations pour une évidence future sont
`DOCUMENTARY_BINARY_ENCODING`, `DOCUMENTARY_MASTER_READOUT` et
`DOCUMENTARY_BINARY_PROGRESS`, portés par les déclarations ci-dessus.
L'enregistrement figé attend un commit de référence selon la procédure du dépôt.

Ce raccord ferme le premier choix documentaire entre deux sources. Les lots 2
et 3 continuent avec les obligations de section, leurs dépendances et les règles
de déduction de la classe entière. Le lot 4 doit composer le progrès et sa borne
pour toute politique, y compris les propositions absentes ou valides sans progrès.
Les futurs documentaires, l'oubli de mémoire sous ce contrat, la sauvegarde et
le chargement durable appartiennent aux lois supplémentaires du lot 5.
L'intégration du modèle local et les effets de fichiers suivent au lot 6 ;
la comparaison avec et sans le dispositif suit au lot 7.
