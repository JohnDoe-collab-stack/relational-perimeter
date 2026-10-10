# Restauration exacte du stockage documentaire depuis des octets

Le chargement restitue exactement le stockage documentaire de toute exécution
finie de la classe canonique : types des occurrences, valeurs, producteurs,
arbre de formation et lecteurs de justification. La preuve couvre les
programmes mixtes, les politiques adaptatives totales et les séquences finies
de requêtes mémoire déjà déclarées. Elle ne suppose pas que la tâche réussit.

Cet incrément du lot 6 ferme un composant de la sauvegarde du présent complet.
Le curseur maître et les autres composants du présent restent à sérialiser.
Le résultat est une preuve Lean et un smoke test de reprise physique ; ce
n'est pas une nouvelle expérience Qwen ni la clôture du lot 6.

## Configuration et portée

Les paramètres sont les sources reçues, leur contexte de références typées,
le contrat de citations et le catalogue de règles avec ses permissions. Ils
restent identiques entre sauvegarde et chargement. Le théorème est générique
en ces paramètres ; les essais physiques utilisent la configuration antérieure.

La classe `CanonicalRestoration.Formed` commence au stockage vide et utilise
les producteurs existants de dépôt de citation et de déduction binaire. Une
citation reprend la localisation positive et la permission effectivement
renvoyée par le résolveur. Une déduction conserve l'action réellement formée,
ses deux ports antérieurs et sa permission. La preuve de restauration ne prend
pas un aller-retour réussi comme hypothèse : elle le dérive par récurrence sur
cette histoire de formation.

Un stockage initial déjà constitué doit appartenir à cette classe. Cette
condition est fermée par le constructeur vide dans les réalisations concrètes.
Les refus et les dépendances manquantes ne créent pas d'occurrence. Les
productions supplémentaires et les sorties autorisées qui manquent leur but
restent dans le stockage et font partie de l'égalité restaurée.

Le schéma 2 encode ce stockage seul. Il utilise le codec d'octets déjà prouvé,
avec version 1 et champs de session vides. Le chargeur refuse une autre
version, un autre schéma, un en-tête incompatible, des octets mal formés, une
source ou règle interdite, une référence absente et une valeur altérée.
La configuration reçue n'est pas incluse dans ces octets. La validation de
cohérence n'établit pas l'authenticité cryptographique d'un fichier.

## Chaîne formelle

| Passage | Construction ou résultat Lean |
| --- | --- |
| Position vers occurrence | `CanonicalRestoration.locate_reference` retrouve le type et la référence positive d'origine |
| Citation réelle | `packet_output` et `packet_permission` consomment les champs d'exactitude du paquet maître ; `packet_formed` reprend sa sortie réelle |
| Déduction réelle | `decision_formed` consomme la décision passée, son action et son équation d'exécution ; le refus conserve l'histoire précédente |
| Histoire canonique | `store_roundtrip` établit l'égalité du stockage dépendant, y compris sa formation et ses lecteurs de justification |
| Programme réel | `execution_store_roundtrip` consomme les étapes de la trace existante, indépendamment de l'accomplissement du but |
| Octets | `PortableStore.byte_roundtrip` compose la loi du codec physique et la restauration exacte du stockage |
| Politique adaptative | `CanonicalAdaptiveRestoration.execution_byte_roundtrip` couvre les détours, leurs productions conservées et les effacements de contexte |
| Requêtes mémoire | `memory_execution_byte_roundtrip` couvre toute trace finie du langage `Memory.Request` : progrès, lecture, statut et reset |

Le chargement construit directement les témoins `Formation` et `Justified`
après validation. Il n'appelle pas les opérations historiques `quote`, `form`,
`execute`, `Program.step`, ni la recherche maître. Les preuves de rattachement
des traces utilisent leurs équations d'exactitude ; elles ne modifient pas
l'exécution opérationnelle existante.

`PortableStore.store_continuations` donne également l'accord de toute fonction
qui consomme ce stockage seul après l'aller-retour. Les futurs du présent
complet lisent aussi son curseur, ses liaisons, sa file, son contexte et ses
observations. Leur accord depuis un fichier exige encore la restauration de
ces composants.

## Pourquoi les valeurs ne suffisent pas

`PortableStoreCases.equal_records_different_formations` construit deux
stockages cohérents avec les mêmes enregistrements et les mêmes valeurs.
Dans le premier, une seconde citation est déposée depuis le paquet ; dans
l'autre, un producteur lit la première occurrence. L'un possède zéro port
d'entrée, l'autre un port. Les stockages sont donc démontrés distincts.

Ce contre-exemple explique la condition de langage canonique. On ne peut
étendre cette preuve à tout producteur d'ordre supérieur en conservant
seulement les étiquettes et les valeurs. Pour restaurer le curseur maître,
il faut une présentation de ses producteurs et de leurs dépendances dont
l'interprétation retrouve les formations effectivement conservées.

## Essais et reproduction

Le smoke test fige trois graphes littéraux indépendants : parcours normal,
propositions hostiles avec une production supplémentaire de zéro, et
prémisses inversées avec une production supplémentaire de moins un. Seize
cas combinent huit politiques et deux modes d'effacement de contexte.

Chaque cas sauvegarde les octets de son exécution adaptative réelle, termine
son processus, puis les charge dans un autre processus qui n'importe ni le
module de démarrage ni les cas fermés. Le stockage est réécrit à l'identique.
Une nouvelle somme lit deux fois sa dernière occurrence et produit quatre ;
ses ports et ses octets sont comparés au graphe attendu. Treize mutations
sont refusées avant toute écriture de sortie ou continuation.

Le contrôle du C généré examine les 27 corps accessibles par appels directs
depuis le chargeur et rejette deux injections de production historique. Sa
portée est ce graphe d'appels directs ; les fermetures indirectes,
l'initialisation globale et l'identité du tas n'y sont pas certifiées.
Les effets physiques passent par Lean IO, le runtime, le système de fichiers
et le système d'exploitation. Les preuves portent sur les fonctions pures.

```text
lake build Tests.LocalAlignment.DocumentaryPortableStoreCases
python -B scripts/check-documentary-portable-store-codegen.py
python -B scripts/run-documentary-portable-store-smoke.py
```

Les quatre modules nouveaux comportent 66 références sélectionnées sans
axiome. Les vérifications et empreintes de cet incrément sont consignées
dans [son relevé](restauration-stockage-documentaire-verification.json).
Le candidat `DOCUMENTARY_CANONICAL_STORE_BYTE_FIDELITY` reste en développement
non commité ; sa revue indépendante n'est pas enregistrée. Les relevés
antérieurs conservent leurs propres arbres et empreintes.

## Obligation suivante du plan

Restaurer ensemble le curseur et ses ressources maître, la mémoire du dossier,
ce stockage, les liaisons, la file restante, le compteur, le contexte et le
dernier résumé. Le chargement doit aussi identifier la configuration reçue.
L'égalité du présent chargé permettra ensuite de raccorder les lois existantes
d'admissions, d'événements, de lectures et d'accomplissement de tous les futurs
finis déclarés. La reprise physique devra produire de nouvelles citations et
déductions depuis ces ressources, puis recevoir les propositions de Qwen.
