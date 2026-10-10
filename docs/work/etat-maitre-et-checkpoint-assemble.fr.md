# État maître depuis des octets et checkpoint assemblé

Ce raccord ferme la restauration de l’état transmis par la machine :
assignation avec lecteur mesuré, génération, graine de recherche, décisions
ordonnées et provenance. Il ferme aussi les codecs des constitutions libres
et des histoires enracinées. Les égalités Lean portent sur les valeurs
dépendantes entières ; les reprises physiques exécutent ensuite une étape
nouvelle à partir des champs chargés.

Le présent documentaire est désormais assemblé dans un paquet qui réunit
l’état source, le stockage, la mémoire du dossier et le contrôle. Sa restauration
restitue le présent entier et conserve ses futurs déclarés. Le paquet contient
encore un payload maître typé : les valeurs historiques de découverte,
d’application, de décomposition et les environnements de producteurs ne sont
pas tous représentés en octets. La reprise du présent entier depuis un fichier
seul reste donc une obligation. Les lots 6 et 7 demeurent ouverts.

Ce document et son [relevé de vérification](etat-maitre-et-checkpoint-assemble-verification.json)
décrivent un incrément de développement non commité sur
`codex/ai-alignment-under-contract`, à partir de la révision
`f30196e4a8ae2b77b0d061c1e03cccd236265013`. Il prolonge le
[raccord de l’assignation séquentielle](assignation-sequentielle-portable.fr.md),
sans actualiser ses empreintes ni celles des évidences antérieures.

## Ce qui est restitué

| Composant | Données chargées et portée de l’égalité |
| --- | --- |
| Constitution libre | Arbre reçu des constructeurs racine et formation ; curseur, différence de bord, terme de formation compatible, obstruction et provenance restitués dans la présentation reçue. |
| Histoire enracinée | Constructeurs successifs et endpoint enregistré à chaque étape ; validation de leur connexion et restauration de l’histoire complète avec ses témoins de génération. |
| Génération | Cible constituée reçue, indice dépendant et quatre compteurs conservés tels quels ; étape générée et certificats restitués exactement. |
| État transmis | Recette de l’assignation et du lecteur, génération, graine, décisions avec valeurs et ordre, provenance avec répétitions ; restauration de l’état dépendant complet sans recevoir l’ancien état. |
| Stockage et mémoire documentaire | Codecs existants de leurs occurrences et formations canoniques, utilisés sur les données chargées. |
| Contrôle | Slots, liaisons optionnelles, file typée restante, contexte, compteur et dernier résumé, reconstitués relativement au stockage chargé et au critère final reçu. |
| Présent assemblé | État source effectivement décodé et installé dans le maître ; autres valeurs, formation et producteurs conservés par le payload typé ; présent entier restitué. |

Les cinq nouveaux formats portent respectivement les tags 90, 91, 92, 93 et
94, avec version 1. Le dernier contient quatre sections d’octets de longueur
explicite : source, stockage, mémoire et contrôle. Les chargeurs exigent
l’épuisement de l’entrée. Le codec d’octet refuse une valeur supérieure à 255.

## Constitution et histoire

[FoundationPortable](../../Tests/LocalAlignment/DocumentaryFoundationPortable.lean)
parcourt la constitution conservée. Son interprète reconstruit directement les
champs des constructeurs, sans appeler le générateur historique.
`capture_exact` prouve l’égalité de la constitution complète. Les champs
non enregistrés séparément sont déterminés par les égalités obligatoires de
leurs constructeurs : leur restitution exacte est démontrée par élimination
de ces égalités.

L’arbre est enregistré, plutôt qu’un nombre donnant instruction de produire
une constitution. La profondeur sert à vérifier un indice dépendant. Cette
lecture quantitative intervient après la capture des constructeurs.

[HistoryPortable](../../Tests/LocalAlignment/DocumentaryHistoryPortable.lean)
conserve les endpoints successifs. Le chargeur vérifie que chaque endpoint
est le successeur constitué du précédent et matérialise le endpoint reçu.
Les lemmes d’unicité des témoins imposés par `GeneratedStep` ferment
l’égalité de l’histoire entière. `restored_exact` couvre toute histoire
enracinée dans la présentation reçue.

La projection d’histoire depuis le curseur lit celle conservée dans la dernière
étape d’un préfixe avancé. Au constructeur racine, la source est un indice
dépendant effacé à l’exécution ; cette projection retourne `none`.
Elle ne prétend pas disposer d’une valeur retenue dans ce constructeur.
Le codec générique accepte néanmoins toute histoire effectivement fournie,
y compris une histoire racine.

## Génération, décisions et provenance

[GenerationPortable](../../Tests/LocalAlignment/DocumentaryGenerationPortable.lean)
enregistre la cible constituée et les quatre champs de travail présents dans
`CanonicalStageGeneration`. Il valide la cible par rapport à l’indice,
puis reconstruit les champs de l’étape et leurs certificats.
`restored_exact` restitue la génération entière. Les compteurs 7, 8, 9 et
10 sont notamment conservés dans un cas de contrôle : le codec ne les remplace
pas par les compteurs d’un nouvel appel au générateur.

[StatePortable](../../Tests/LocalAlignment/DocumentaryStatePortable.lean)
charge une recette finie de l’assignation et du lecteur dans la classe positive
de l’incrément précédent. Il construit les invariants de cette assignation,
puis vérifie la graine de recherche, la correspondance ordonnée entre décisions
et provenance, et la valeur de chaque décision. Ces contrôles parcourent les
données finies ; ils n’interrogent pas le lecteur mesuré.

Des décisions compatibles répétées restent répétées. Aucun ensemble ou
dédoublonnage ne remplace l’histoire. `restored_exact` prouve une égalité
du triplet dépendant profondeur, assignation et état transmis entier.

La possibilité d’exécuter la prochaine étape fait l’objet d’un contrôle
séparé. `restore` admet un état valide dont une décision touche une variable
future ; `restoreForNext` exige en plus la fraîcheur requise par l’exécuteur.
Ce contrôle ne change pas la définition générale d’un état valide.

[StateCapture](../../Tests/LocalAlignment/DocumentaryStateCapture.lean) capture
l’état effectivement lu par le curseur. Les lois `finite_master`, `program`,
`adaptive` et `memory` couvrent les traces finies déclarées depuis un curseur
`Ready`. La fermeture de cette classe et sa racine publique sont fournies
par le raccord séquentiel existant. Le chargeur de l’état ne reçoit ni le
curseur d’origine ni ses autres champs.

## Assemblage et futurs

[AssembledCheckpoint](../../Tests/LocalAlignment/DocumentaryAssembledCheckpoint.lean)
réunit les quatre sections avec le maître typé conservé. La restauration
parse le fichier, charge l’état source, installe cet état réellement décodé
dans le support du maître, puis charge le stockage et la mémoire. Le contrôle
est décodé sur ce stockage chargé.

Le certificat du paquet lie sa section source à l’état du maître conservé.
Les ports, les anciennes valeurs et la formation sont transportés avec cette
égalité ; aucune opération historique n’est appliquée pour reconstruire son
résultat. Ce certificat est une donnée typée du paquet. Il n’est pas une
signature cryptographique ni une preuve d’authenticité d’un fichier arbitraire.

`restored_exact` prouve l’égalité du présent entier sous les témoins positifs
`Ready`, `CanonicalRestoration.Formed` et `PortableMemory.Formed`.
Le contexte fournit son codec exact ; les sources, le contrat, le catalogue
de règles et le critère final restent les paramètres reçus.

`all_futures` conserve le résultat de toute suite finie de requêtes du langage
mémoire déclaré. `accomplishment` transporte le témoin positif de possibilité
d’accomplissement. Dans [AssembledCases](../../Tests/LocalAlignment/DocumentaryAssembledCases.lean),
les traces finies depuis la racine documentaire fournissent effectivement
les témoins de fermeture du stockage, de la mémoire et de l’état source.
Ces lois ferment l’assemblage du paquet hybride. Elles ne ferment pas la
matérialisation des environnements maître historiques depuis des octets.

## Vérifications de développement

`scripts/run-state-assembly-smoke.py` utilise un processus initial qui reçoit
la racine publique existante, puis trois processus de reprise froide sans
importer cette racine. Ils chargent les cas réel, de voie inadaptée et de source
bloquée. Chacun retrouve l’état source entier et exécute une nouvelle découverte
puis une nouvelle étape sur les décisions, la provenance, la génération et la
graine chargées.

Ces processus chargent également la constitution, la génération et l’histoire,
puis exécutent de nouvelles générations et extensions d’histoire. Les oracles
Python indépendants fixent les mots du format, les bits, les mesures du lecteur
et les champs avant et après l’étape. Trois sources supplémentaires vérifient
des compteurs différents, des décisions compatibles répétées et une composition
de visite et retournement. Dix-huit entrées malformées ou incompatibles sont
refusées.

Le test d’assemblage écrit et relit le fichier dans le même processus, en gardant
le payload maître typé. Après chargement, reset et progression terminent la
citation et la somme restantes : compteur 5, file vide. Les octets finaux du
stockage, du contrôle et le relevé complet de l’état source sont identiques à
ceux de la continuation directe. Ce test ne constitue pas une reprise froide
du maître entier.

`scripts/check-state-assembly-codegen.py` inspecte 29 chemins directs du C
compilé, objets constants compris, avec les noms `l_` et `lp_`.
Il rejette 104 injections de producteurs historiques, d’étapes, de lectures
ou d’applications indirectes interdites. Les callbacks des codecs parcourent
les mots finis. Cette inspection porte sur les chemins désignés ; elle
ne certifie pas l’initialisation de tout processus ni le coût physique.

Tous les clients runtime sont audités sans axiome. Deux pièges ont été corrigés :
une lecture depuis l’indice du préfixe racine relançait la construction
canonique ; la capture lit désormais une histoire matériellement retenue.
Des lemmes de bibliothèque sur les octets et la concaténation de chaînes
introduisaient des axiomes dans les audits ; les octets bornés sont construits
directement et les clients reçoivent leurs chemins complets.

Les contrôles suivants sont intégrés aux deux scripts de vérification :
```text
lake build Tests.LocalAlignment.DocumentaryAssembledCases
python -B -X utf8 scripts/check-state-assembly-codegen.py
python -B -X utf8 scripts/run-state-assembly-smoke.py
powershell -NoProfile -File scripts/verify.ps1
```

La gate complète passe sur 296 fichiers Lean : 25 352 constantes dans 295
modules, aucune exception écrite aux audits et 23 fixtures de refus conformes.
Les 364 exceptions générées historiques restent inchangées. Les huit processus
du nouveau smoke vérifient au total 58 audits runtime sans axiome.
Le relevé joint conserve les résultats, reçus et empreintes de cette gate.
Les expériences restent des smoke tests de développement. Aucun appel Qwen ni
protocole comparatif du lot 7 n’a été exécuté par cet incrément.

## Travail encore nécessaire pour le fichier autonome

Il reste à encoder les valeurs historiques complètes de découverte,
d’application et de décomposition, les préfixes opérationnels, les têtes,
les environnements dépendants des producteurs et leur formation entière.
Les codes d’opération et les positions de ports déjà portables ne suffisent
pas à reconstruire ces valeurs.

La difficulté concrète est dans leurs champs : résultats de recherche,
extractions et mesures, contextes relationnels, continuations et lecteurs,
sorties exécutées et témoins indexés par ces sorties. Le prochain passage
doit les capturer puis les restituer directement. Une recette qui réexécuterait
la recherche ou l’application passée ne fermerait pas cette obligation.

Une fois ces codecs fermés, le paquet devra remplacer son payload typé par
une section maître autonome, reconstruire ses ports et producteurs à partir
des données chargées, puis vérifier la reprise du présent complet dans un
nouveau processus. Les garanties de contrat, d’oubli et d’accomplissement
devront alors être raccordées à cette réalisation entière.
