# Reprendre une déduction depuis un checkpoint effectivement sauvegardé

Un premier cas de reprise physique est réalisé. Le processus initial exécute
quatre instructions du dossier reçu : une citation de la mesure 42, une citation
de sa révision 43, leur différence, puis une nouvelle citation de la mesure 42.
Il sauvegarde le présent de ce calcul et termine. Un autre processus charge
les octets, restaure les ressources et leurs formations, puis effectue la somme
de la différence avec elle-même. Il écrit le dossier justifié et les
ressources finales. Ce dossier et ces ressources coïncident avec ceux de
l'exécution continue.

Ce raccord ferme un premier cas du lot 6. La reprise générale du présent
documentaire adaptatif, avec de nouvelles citations et la continuation du maître,
reste une obligation du plan. Les lois générales du
[lot 5](memoire-documentaire-et-futurs.fr.md) restent celles du présent typé ;
leur transport à une réalisation portable complète demande encore sa preuve.

## Le contrat exact de cette reprise

La configuration reçue est celle du dossier existant : trois positions de
sources, dont les positions 1 et 2 sont autorisées ; trois occurrences de règles,
dont les positions 0 et 1 sont autorisées. La troisième règle reproduit
l'opération de la première, mais son occurrence 2 reste interdite. Les passages,
versions, demandes et autorisations sont identiques aux cas précédents ;
`same_sources`, `same_contract` et `same_rules` ferment cet accord.

Le checkpoint porte quatre couches de ressources, les quatre liaisons de tâches,
le compteur 4, la profondeur observée 3 et l'identifiant de l'unique tâche restante.
Cette tâche est la somme de la différence avec elle-même, avec valeur exigée 2,
règle exigée à la position 1 et origines exigées `[1, 2, 1, 2]`. Le chargeur
vérifie la version, le schéma, cette frontière et cette tâche. Il reçoit la
configuration fixée par le programme ; le numéro de schéma n'est pas une preuve
d'authenticité du fichier ou du programme installé.

Ce contrat n'offre pas de nouvelle extraction, de nouvelle politique de
proposition ou de changement de catalogue. Le curseur du maître n'est pas
remplacé par un curseur initial : il n'est pas un champ de l'état restauré.
La déduction restante n'en a pas besoin. Sa profondeur conservée est une
observation du préfixe, et `remaining_does_not_advance_master` établit que la
continuation correspondante du programme original ne l'avance pas.

## Ce qui est restauré

Une couche enregistrée est une citation avec sa position source et sa valeur,
ou une déduction avec sa position de règle, les positions ordonnées de ses
prémisses dans le tuple antérieur et sa valeur. Les couches sont enregistrées
de la plus récente à la plus ancienne. Le chargement restaure d'abord leurs
prémisses, résout les références dans les contextes reçus et consomme les témoins
positifs de permission.

Le chargement compare chaque valeur sauvegardée à l'équation déclarée de sa
couche. Cette vérification arithmétique est exécutée ; elle ne relance pas la
recherche maître, l'extraction documentaire ou le producteur historique.
`restoreQuotation` et `restoreDerived` placent la valeur sauvegardée dans le
tuple et construisent directement son témoin de formation. La base vide seule
est un support donné. Les ressources produites conservent leurs couches de
production et les ports dont elles dépendent.

L'enregistrement des valeurs et des sortes ne suffit pas, à lui seul, à prouver
la fidélité pour un producteur fonctionnel arbitraire. Le langage de restauration
est celui des producteurs canoniques de citations et de règles binaires. Pour
le préfixe réellement exécuté de ce cas, `actual_formation_recovered` établit
l'égalité du support restauré avec le support original. Cette égalité porte
aussi sur l'arbre de formation et ses producteurs. Elle ne se limite pas à
une comparaison des nombres ou des étiquettes d'origine.

Les liaisons sont chargées à leurs positions sauvegardées, puis validées contre
les demandes reçues. Une valeur égale ailleurs ne sert pas de remplacement.
`Table.complete` construit les réalisations de toutes les tâches retenues à
partir de ces liaisons vérifiées. Deux citations égales de 42 restent deux
occurrences distinctes.

## La tâche restante et son certificat

`finish` exécute une seule fois la déduction sur les prémisses restaurées.
Il conserve la décision réellement obtenue, l'incorporation de ses ressources
et l'occurrence délivrée. La preuve d'accomplissement consomme cette action et
les critères des prémisses. Pour tout `Loaded` du schéma, `continuation_value`
et `continuation_origins` donnent la valeur 2 et les origines demandées.

Sur le checkpoint du préfixe réel, `restarted_formation_same` établit en plus
l'égalité de la formation finale avec celle du programme original poursuivi
sans arrêt. Le contenu du dossier est rendu depuis l'occurrence délivrée et
ses justifications : valeur, position locale, origines, occurrences des règles,
identités des documents, versions et textes des passages. Les octets publiés
ne proviennent pas d'une phrase attendue substituée à ce résultat.

## Codec et réalisation sur disque

Le codec de référence utilise l'alphabet d'octets 0, 1, 2, avec signes et
longueurs explicites. Son codage unaire facilite l'audit constructif. Il ne
revendique aucune efficacité de stockage. `codec_roundtrip` prouve l'aller-retour
pour tout enregistrement `Saved`, avant la validation du contrat. `encode_alphabet` établit que seuls les
symboles 0, 1 et 2 sont émis ; `physical_byte_codec_roundtrip` ferme aussi
leur conversion en `UInt8` et leur relecture, utilisée par le client réel. Les erreurs
de syntaxe, les octets tronqués ou supplémentaires et les index négatifs sont
traités par le décodeur. La restauration vérifie ensuite permissions,
références, équations et liaisons.

L'[adaptateur](../../apps/local-alignment/documentary-checkpoint.py) distingue
les clients de démarrage, de continuation continue et de reprise. Le client de
reprise importe le codec et le noyau de restauration ; il n'importe ni le
module de démarrage ni les cas fermés contenant le préfixe exécuté. Le client
de démarrage ne contient pas l'exécution de la dernière déduction.

Chaque client écrit dans l'espace reçu. L'adaptateur relit les fichiers et
conserve leurs tailles et empreintes, ainsi que l'identifiant du processus et
l'empreinte du client utilisé. Ces reçus attestent les fichiers effectivement
lus dans l'essai ; ils ne constituent pas une signature de leur origine.
Un fichier alternatif cohérent peut passer la validation mathématique.

Les écritures du checkpoint, du dossier et du résultat sont des effets Lean IO.
Leur réalisation relève du compilateur, du runtime, du système de fichiers et
du système d'exploitation. Cet incrément teste une fin de processus suivie
d'un chargement réussi ; il n'établit pas l'atomicité des écritures multiples
ni la résistance à une coupure électrique.

## Vérification

Le [test physique](../../scripts/run-documentary-checkpoint-smoke.py) compare
les fichiers à un oracle littéral indépendant : checkpoint de 235 octets,
dossier de 379 octets et ressources finales de 265 octets. Il utilise 25
processus : démarrage, reprise, continuation continue, deuxième reprise,
liaisons alternatives conservant les occurrences égales, et 20 refus.
Chaque client audite cinq déclarations exécutables. La gate complète passe sur
266 fichiers Lean et 23 624 constantes, avec les 120 nouvelles déclarations
auditées, aucune exception écrite et les 23 refus historiques conformes. Les refus portent notamment
sur une version différente, une tâche différente, une valeur altérée, une source
privée, la règle dupliquée interdite, une prémisse absente, une liaison incorrecte
et des octets invalides. Aucun refus ne publie de dossier ou de résultat.

Le [contrôle du code compilé](../../scripts/check-documentary-checkpoint-codegen.py)
examine les 23 corps accessibles par appels C directs depuis le chargeur : aucun
appel de production n'est accessible dans cette portée. La continuation a un
site d'appel du déducteur. L'injection d'un rejeu dans le chargeur et celle d'un
second appel dans la continuation sont rejetées. Ce contrôle délimité ne vaut
pas audit de toutes les initialisations ou de tous les appels indirects du
processus ; la fidélité constitutive du cas est également fermée en Lean.

Les preuves se trouvent dans
[DocumentaryPortable](../../Tests/LocalAlignment/DocumentaryPortable.lean),
[DocumentaryPortableCheckpoint](../../Tests/LocalAlignment/DocumentaryPortableCheckpoint.lean),
[DocumentaryPortableStart](../../Tests/LocalAlignment/DocumentaryPortableStart.lean)
et [DocumentaryPortableCases](../../Tests/LocalAlignment/DocumentaryPortableCases.lean).
Les vérifications de cet incrément sont enregistrées séparément dans le
[relevé](checkpoint-documentaire-portable-verification.json). Les seize modules
documentaires antérieurs et leurs sept relevés sont conservés sans modification.
L'incrément demeure en développement, sans révision de preuve commitée ni revue
indépendante enregistrée. Aucun nouvel essai Qwen n'est revendiqué.

## Reproduire

Depuis la racine du dépôt, avec le Python configuré et la chaîne Lean épinglée :

```text
lake build Tests.LocalAlignment.DocumentaryPortableCases
python scripts/run-documentary-checkpoint-smoke.py
python apps/local-alignment/documentary-checkpoint.py start mon-espace
python apps/local-alignment/documentary-checkpoint.py resume mon-espace
```

Le dossier réalisé est `mon-espace/dossier.md`. Les commandes séparées terminent
leurs processus respectifs ; la seconde consomme `mon-espace/checkpoint.bin`.
L'essai automatique crée ses espaces temporaires hors du dépôt. La gate complète
inclut désormais ce contrôle et le contrôle du code compilé.

La prochaine fermeture nécessaire concerne le présent adaptatif complet :
encodage des ressources maître réellement retenues, conservation des observations
de politique et accord de tous les futurs documentaires depuis les octets
chargés, avant d'élargir cette reprise aux tâches mixtes restantes.
