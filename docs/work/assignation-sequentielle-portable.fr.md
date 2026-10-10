# Assignation séquentielle restaurée avec ses invariants

Cet incrément du lot 6 ferme la restauration de l’assignation séquentielle
complète : fonction d’assignation, lecteur mesuré, bit initial vrai et invariants
sur toutes les variables futures sélectionnées et d’ancrage. Les données chargées
permettent ensuite d’exécuter une nouvelle étape opérationnelle.

La classe portable est positive et finie dans sa description. Sa primitive
est l’assignation alternée déjà employée par le maître. Une recette conserve
chaque retournement et chaque visite de lecteur, dans leur ordre. À la profondeur
courante, tous les retournements doivent porter sur des variables strictement
positives et antérieures à la prochaine variable sélectionnée. Le décodeur
contrôle cette condition sur la recette ; il en construit les preuves requises.

L’assignation chargée est aussi incorporée comme champ exécutable d’un état
maître dont les autres champs sont encore fournis par le support conservé.
Le raccord prouve l’égalité de l’état couplé entier. Le chargement physique
des autres ressources maître et du présent adaptatif reste ouvert.

Identifiant candidat : `DOCUMENTARY_SEQUENTIAL_ASSIGNMENT_BYTES`.
Le [relevé de développement](assignation-sequentielle-portable-verification.json)
identifie cet arbre non commité. Les registres et évidences précédents gardent
leurs propres snapshots ; aucune nouvelle revue indépendante n’est enregistrée.

## Pourquoi la vérification est finie

Dans la famille canonique reçue, la prochaine variable sélectionnée est égale
à 2 × (profondeur + 4) + 2. Cette formule est une lecture démontrée de la
génération constituée ; elle sert seulement au contrôle du chargement. Les labels
sauvegardés restent ceux des découvertes réellement conservées dans le support.

Un retournement sur une variable positive préserve le bit zéro. Un retournement
strictement antérieur à la prochaine variable laisse inchangées toutes les
variables sélectionnées et d’ancrage futures. Les visites modifient le travail
du lecteur, tout en conservant l’assignation. La récurrence sur la recette ferme
donc les trois invariants, pour tous les futurs concernés, sans les vérifier
un par un et sans interroger la fonction reconstruite pendant le chargement.

La condition définit une classe suffisante. Elle n’est pas un décideur de
validité de toutes les assignations possibles : deux retournements de zéro
seraient annulés sur les bits, mais leur recette est refusée dans cette classe.
Cette frontière ne réduit pas le codec précédent du couple assignation/lecteur,
qui continue à restituer toute recette de son langage.

## Fidélité de la constitution exécutée

La capture réutilise celle du
[couple assignation et lecteur](assignation-lecteur-portables.fr.md).
Elle lit les codes de transport effectivement retournés et conservés dans les
têtes du support, avec le label stocké dans chaque découverte. Les visites
d’identité et de composition restent présentes ; une égalité des seuls bits
ne les remplace pas.

La condition de chargement est conservée par toute étape séquentielle reçue
depuis une recette sûre. La preuve consomme l’accord entre la découverte
effective et la variable sélectionnée de cette étape. Elle traite toute
structure de code de transport reçue dans le type déclaré.

La fermeture se compose sur les exécutions finies du maître, des programmes
documentaires, des politiques adaptatives et des requêtes mémoire. Les refus,
les tâches inadéquates, les productions supplémentaires et les resets sont
inclus. Les théorèmes demandent au départ l’égalité exacte de la recette avec
l’assignation/lecteur et sa condition de sûreté à la profondeur reçue.
Cette hypothèse est fermée sur l’origine publique existante, ainsi que sur
les états initiaux de la famille alternée.

La restauration obtient une égalité du SequentialAssignment entier,
à profondeur fixée. Les preuves contenues dans cet objet sont propositionnelles :
l’identité entière découle du couple fonction/lecteur exact et de l’irrélevance
des preuves du noyau. Aucune extensionnalité de fonctions n’est utilisée.
Tout consommateur de l’objet ainsi restauré retrouve donc exactement son résultat.

## Incorporation dans l’état maître conservé

Le raccord lit dans l’état reçu sa génération, sa graine de recherche,
ses décisions et sa provenance. Il installe l’assignation décodée dans le champ
d’assignation exécuté et transporte les preuves dépendantes. L’égalité démontrée
porte sur le couple assignation/état entier, puis sur chacun de ses consommateurs.

Le raccord reçoit les octets avec une preuve qu’ils sont ceux de la recette
capturée. Cette preuve autorise le transport dépendant ; elle ne fournit pas
une authentification cryptographique. Le chargement isolé, lui, accepte toute
recette du schéma qui satisfait la condition de classe. Des octets différents
mais bien formés peuvent donc constituer un autre objet valide.

Les autres champs de l’état restent reçus sous forme typée. Ce passage clôt
l’incorporation de l’assignation chargée ; il ne les décode pas depuis un fichier.

## Schéma et reprise physique

Le schéma reçoit le marqueur 89, la version 1, la profondeur et la liste de
commandes du lecteur. Le codec des commandes est réutilisé. Le chargement exige
la consommation entière des mots et des octets, puis vérifie les bornes de
chaque retournement. Le consommateur à profondeur fixée refuse une autre profondeur.

Le smoke exécute les trois programmes existants depuis le même cadre initial :
complet, inadéquat et refus avec dépendance absente. Leurs profondeurs et recettes
sont respectivement 3 avec [14, 12, 10], puis 2 avec [12, 10] dans les deux autres cas.

Dans le processus de départ, chacun de ces trois composants est sauvegardé,
rechargé et incorporé dans son état conservé. Une nouvelle étape consomme
le champ d’assignation décodé de cet état. Trois processus nouveaux reçoivent
ensuite uniquement les octets et produisent eux aussi une nouvelle étape
depuis l’assignation séquentielle chargée. Ils ne reçoivent pas les états
de génération, décisions ou provenance historiques.

Quatre reprises supplémentaires traitent la primitive, deux visites,
deux retournements identiques et une forme de composition. Au total,
sept nouvelles étapes sont exécutées après reprise froide, ainsi que trois
après incorporation dans le processus de départ. Les lectures portent sur
quatorze variables, comprenant les variables nouvellement retournées.
Les bits, visites et comparaisons unaires avant et après la nouvelle étape
sont comparés à des oracles séparés ; les octets sont comparés au schéma littéral.

Vingt et une entrées invalides sont refusées, dont zéro, la prochaine variable
et une variable ultérieure. Le smoke utilise neuf processus physiques et
audite sans axiome sept, six et trois déclarations dans ses trois clients.
Il n’appelle aucun modèle local et reste une vérification de développement.

## Chaîne formelle et contrôles

| Passage | Module et déclarations |
| --- | --- |
| Classe positive et invariants futurs | `DocumentarySequentialPortable` : `Safe`, `safe_zero`, `safe_above`, `assemble` |
| Égalité de l’objet dépendant | `sequential_injective`, `assembled_exact` |
| Fermeture sur le code effectivement retourné | `reflect_safe`, `stage_safe`, `stage_formed` |
| Octets et futurs de l’assignation | `byte_roundtrip`, `formed_roundtrip`, `restore_at_exact`, `all_typed_consumers` |
| Traces réelles du maître et du dossier | `DocumentarySequentialCapture` : `executed_ready`, `program_ready`, `adaptive_ready`, `memory_ready` |
| Champ chargé dans l’état conservé | `incorporateState`, `restoreState`, `restored_state_exact`, `all_state_consumers` |
| Origine publique et refus de frontière | `DocumentarySequentialCases` |

Les trois modules portent 78 déclarations sélectionnées sans axiome.
Les dix graphes d’appels directs du code compilé couvrent le contrôle fini,
la reconstruction des fonctions latentes, les loaders, l’incorporation et
la capture du code de l’étape. Vingt et une injections de production historique,
de génération ou de lecture prématurée sont rejetées. Les callbacks du codec
portent sur des mots de premier ordre. Cette inspection garde sa portée
d’appels nommés directs et ses frontières de runtime et d’initialisation.

    lake build Tests.LocalAlignment.DocumentarySequentialCases Tests.AllConstantsAudit
    python -B -X utf8 scripts/check-sequential-codegen.py
    python -B -X utf8 scripts/run-sequential-restart-smoke.py

Les deux gates du dépôt incluent ces contrôles. La gate complète exécutée
sur cet incrément passe : 289 fichiers Lean, 291 jobs de build et l’audit
exhaustif de 24 904 constantes dans 288 modules. Les 364 exceptions générées
historiques restent inchangées ; aucune exception écrite n’est admise.
Les 23 fixtures de refus attendu et tous les contrôles de reprise passent.
Les échecs des essais de preuve et de client restent identifiés dans ce relevé.
Aucune borne de coût physique, de temps constant ou d’énergie ne découle
des compteurs symboliques de lecture.

## Suite du lot 6

Il faut maintenant encoder les générations et leurs histoires, les décisions
et provenances, les préfixes opérationnels, les découvertes et applications,
les décompositions et les environnements dépendants des producteurs.
Les ports des recettes maître devront être résolus depuis ces valeurs chargées.

Le maître complet sera ensuite réuni au stockage, à la mémoire documentaire et
au contrôle sous la configuration reçue identifiée. L’accord des futurs et les
nouvelles citations et déductions devront être réalisés depuis ce présent entier
chargé physiquement. L’interface documentaire Qwen et le protocole comparatif
restent également ouverts. Le [plan](plan-alignement-agent-dossier.fr.md)
conserve ces obligations.
