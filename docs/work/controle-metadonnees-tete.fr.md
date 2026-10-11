# Métadonnées payées et supports conservés du maître

Cet incrément poursuit D2 du [plan v0.3](RP_ALIGN_PERSIST_SPEC_v0_3.fr.md).
Il traite les douze sites de lectures natives de métadonnées de tête recensés
dans le [rapport précédent](controle-generation-roles-bornes.fr.md). Le maître,
ses producteurs et la cible d'alignement restent ceux du plan.

## Le calcul caché dans les indices

La voie précédente payait la lecture des arguments et l'opération de chaque
producteur. Mais certaines références et certains contextes récupéraient leur
indice par `producer.arguments support.values`. Ces expressions apparaissent
dans des types dépendants ; leur compilation pouvait pourtant exécuter une
nouvelle lecture des valeurs du support. Le compte des opérations explicites
ne couvrait pas ces douze appels.

La nouvelle voie conserve les arguments réellement lus, produit explicitement
l'indice de sortie et conserve le support qui en résulte. Les producteurs
suivants consomment ces champs pour former leurs contextes et leurs références.
Les égalités servent à raccorder leurs types à la spécification originale.

## Ce qui est conservé et démontré

[La construction générique](../../Tests/LocalAlignment/DocumentaryControlConstitutiveResources.lean)
introduit `Cached` et `cachedCode`.

| Passage | Donnée conservée et obligation |
| --- | --- |
| Arguments | Valeurs issues de `argumentsCode`, avec égalité à la lecture des ports reçus |
| Indice | Sortie du `kindCode` contrôlé, avec égalité à l'indice du producteur sur ces arguments |
| Opération | Valeur effectivement produite par le code contrôlé de l'opération |
| Formation | Support entier, avec ses valeurs et son témoin positif `Formation.produced` |
| Nouvelle occurrence | `Cached.here` forme sa référence avec l'indice conservé |
| Occurrences antérieures | `Cached.read_prior` établit la préservation de leur lecture par l'extension |

`Cached.exact` établit l'égalité du paquet conservé entier avec sa constitution
originale. `Cached.read_here` établit que sa nouvelle référence lit la sortie
de l'opération sur les arguments conservés. La préservation d'une lecture
n'identifie pas les occurrences qui possèdent éventuellement la même valeur.

[Le raccord au maître](../../Tests/LocalAlignment/DocumentaryControlMasterHead.lean)
utilise cette voie pour ses sept productions : découverte, application,
décomposition, assemblage de tête, préfixe suivant, source suivante et fraîcheur
suivante. Chacun de leurs indices est formé dans une étape
`producerOutputKind`. La source du curseur suivant vient du support produit ;
les références de préfixe et de fraîcheur sont raccordées à cette source grâce
aux égalités des arguments conservés et aux lois de lecture.

Le résultat de `code cursor` conserve l'égalité au `VariableMaster.masterHead cursor`
entier. Cela inclut la tête, le curseur suivant et l'accord de sa
frontière. `finite` ferme la finitude de cette voie pour tout curseur reçu.
Ces preuves et celles de la construction générique sont sans axiome.

## La borne locale et sa portée

`cached_bounded` donne la borne abstraite

```text
argumentsBound inputs + (kindBound + (operationBound + 3))
```

Elle suppose des bornes fournies pour les codes d'indice et d'opération, pour
tous leurs arguments. Les trois étapes finales forment les valeurs, le témoin
de formation et le support. Les sept codes d'indice concrets du maître ont
chacun une étape suivie d'un retour.

Cette loi compose les coûts déclarés de ces composants. Elle ne fournit pas
l'enveloppe globale du maître, le coût de son bootstrap ou celui du secours.
Les allocations des références et des contextes ainsi que l'administration du
runner doivent encore être intégrées à la fermeture complète de D2 puis D3.

## Contrôles de l'exécution

[La garde C](../../scripts/check-documentary-expanded-control-codegen.py)
rejette les appels directs à `Producer.arguments`, `Support.read` et
`Resources.read` dans les modules de tête et de formation conservée. Elle
contrôle aussi le maintien des arguments, de l'indice, des valeurs et du témoin
dans le paquet compilé, ainsi que les sept continuations d'indice payées.
Il s'agit de contrôles nommés du C et de mutations textuelles de leurs entrées,
sans certification de toute la fermeture transitive ni corruption compilée.

[Le protocole d'intégration](../../scripts/run-documentary-expanded-control-smoke.py)
conserve ses critères de livraison, d'origine, de refus et de progression,
y compris après reset, projection mémoire et chargement. Il exige désormais
sept étapes `producerOutputKind`, puis vérifie le combustible exact, une unité
insuffisante et le surplus. Son plafond de 200 000 sert aux essais ; il n'est
pas une borne de bootstrap démontrée.

La gate complète a réussi sur 342 fichiers Lean et 341 modules :
27 584 constantes auditées, 364 exceptions de génération du compilateur
et aucune exception pour une déclaration écrite. Les 572 audits explicites
des 43 modules de contrôle sont sans axiome. Les 23 fixtures d'échec attendu
conservent leurs diagnostics et sites exacts.

Les gardes étendues rejettent 1 192 mutations textuelles et comptent zéro site
de lecture native de métadonnées de tête et zéro reconstruction native
d'endpoints de schedule dans leur portée. Les 31 contrôles d'intégration,
leurs seize audits runtime, les quatre histoires du bootstrap et leurs
quatre audits runtime passent. Leurs sources et scripts ont été figés avant
la gate ; les 410 empreintes sont restées identiques jusqu'à sa sortie.

La [qualification locale](controle-metadonnees-tete-verification.json)
conserve cette portée et ses empreintes. Elle qualifie un arbre de travail
mutable ; aucune évidence liée à un nouveau commit n'est déclarée.

## Obligations suivantes

| Obligation | État de cet incrément |
| --- | --- |
| Douze lectures natives de métadonnées de tête recensées | Supprimées du C de tête ; réintroduction rejetée dans la portée contrôlée |
| Autres indices exécutables | Projections causales et reconstructions de données à examiner séparément |
| Ouverture documentaire, normalisation, préservation et routage | Moteurs intérieurs restant à instrumenter |
| Requêtes d'assignation et lecteurs différés | Calcul des invocations restant à ouvrir et à raccorder aux frames et codecs |
| Administration, traces, références et allocations | Fermeture complète restant à établir |
| D3 | Enveloppes globales, bootstrap et réserves successorales encore ouverts |
| D4 | `RecoveryData.prepare` utilise encore `Memory.step` nativement ; raccord borné au présent conservé et rechargé restant |

D2 entier demeure ouvert. A conserve sa priorité sur B. Les qualifications
antérieures restent attachées à leurs arbres et ne sont pas réécrites.
