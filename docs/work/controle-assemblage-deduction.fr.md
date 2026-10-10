# Assemblage de déduction depuis les productions conservées

Cet incrément poursuit D2 du [plan d'application](application-alignement-persistant.fr.md)
et de la [spécification v0.3](RP_ALIGN_PERSIST_SPEC_v0_3.fr.md), sur
`codex/align-persist-recovery`, depuis `d61fac4aa81fbfe58be6a1fd1887c91049fb5a3d`.
Il prolonge le [calcul entier et la formation](controle-calcul-formation-documentaire.fr.md).
Ces rapports et leurs relevés restent historiques. La qualification courante
est portée par le [relevé de cet assemblage](controle-assemblage-deduction-verification.json).

Le transport exécuté d'une action de déduction reconstruisait encore le
producteur d'origine. Le nouvel assemblage conserve les ressources réellement
produites, construit le transport depuis le type de sortie effectivement payé
et transmet ces pièces à la frame suivante. Son certificat de progrès lit
la sortie conservée et emploie cette même extension.

## Relecture des obligations du plan

CTRL-02 exige le raccord du compteur aux opérations réelles, avec coûts des
auxiliaires et frontières des primitives annoncés. L'annexe D sépare les lois
de l'interprète, le calcul des enveloppes et l'achèvement du secours. La
réalisation du petit interprète ne clôt donc pas D2 tant que toutes les
opérations du secours ne sont pas raccordées. Les bornes locales construites
ici ne constituent pas encore le bootstrap et les moyens protégés de D3.
A garde la priorité sur B.

Cette vérification a identifié deux constructions supplémentaires dans le C :
les indices exécutables du transport pouvaient recalculer le type de sortie,
et le certificat de progrès pouvait reconstruire son occurrence. Les deux
passages réutilisent désormais les données conservées. Le contrôle du C porte
explicitement sur ces dépendances, en plus des égalités Lean.

## Productions payées et conservation

[ControlAssembly.code](../../Tests/LocalAlignment/DocumentaryControlAssembly.lean)
reçoit une frame documentaire, les occurrences effectivement lues et la
décision effectivement calculée. Après paiement de la sélection de branche,
une décision acceptée traverse les trois références de règle, gauche et droite
avec `ControlReference.positionCode`. Chaque cellule et retour sont comptés.
Ces lectures sont supplémentaires à celles du producteur ; leur coût est
annoncé et aucun gain d'exécution n'est revendiqué.

| Étiquette | Production après paiement |
| --- | --- |
| `assemblyKind` | Type de sortie avec la règle, les occurrences et les trois positions lues |
| `assemblyKinds` | Nouvelle liste de types, avec les anciens types conservés |
| `assemblyKnowledge` | Connaissance portant le support de l'action et la fermeture de justification |
| `assemblyStore` | Stockage portant cette liste et cette connaissance |
| `assemblyExtension` | Transport injectif des anciennes références, avec décalage de position un |
| `assemblyOutput` | Occurrence de sortie dans ce stockage et décision acceptée conservant action et permission |
| `assemblyFrame` | Frame portant stockage, dossier conservé et fonction de liaison |
| `assemblyPacket` | Étape portant cette frame, cette extension et son certificat de progrès |

`extensionFromKind` construit le transport depuis le type payé. Son égalité
avec `FormationAction.transport` est démontrée pour toute action et tout type
conformes. Le constructeur runtime de cette extension n'appelle ni l'ancien
producteur ni `derivedKind` ni une lecture de position native.

La branche refusée conserve le stockage et le dossier reçus, puis paie
l'extension identité, la sortie absente, la frame et le paquet. Elle ne parcourt
pas les références des prémisses et ne construit pas un type de déduction.

[Program.deductionStepFromParts](../../Tests/LocalAlignment/DocumentaryProgram.lean)
emballe les pièces reçues. Les égalités de stockage, extension, sortie et frame
alignent leurs types dépendants. `deductionStepFromParts_actual` prouve l'égalité
avec **l'étape entière** d'origine, y compris son champ de progrès en `Type`.
Le chemin exécuté n'appelle pas `Program.deductionStep` pour établir ce résultat.
Les définitions d'origine et leurs contrats sont conservés.

Le certificat de progrès consomme l'occurrence contenue dans la sortie reçue,
l'extension reçue et le témoin de complétude reçu. Le C de sa nouvelle fermeture
ne reconstruit ni le producteur, ni le type de sortie, ni l'étape d'origine.

## Portée des bornes

`ControlAssembly.bounded` et `finite` couvrent toutes les frames, requêtes,
occurrences et décisions typées de cette interface, sans supposer que le but
est satisfait. Pour une décision acceptée, la borne est :

```text
1 + positionBound(règle) + positionBound(gauche) + positionBound(droite) + 8
```

Une décision refusée coûte cinq transitions. Le résultat conserve l'égalité
avec l'étape d'origine ; `ControlStep.actual_step` et son consommateur de
complétude demeurent raccordés au résultat effectif.

L'unité annoncée est une transition du catalogue abstrait. Certains paquets,
comme une sortie optionnelle ou une frame avec sa fermeture, contiennent
plusieurs constructeurs C. Les huit étapes ne sont ni huit allocations de tas
ni huit instructions physiques. Les fermetures des liaisons et de justification
sont construites ici ; leurs appels ultérieurs ont leurs propres coûts, encore
à instrumenter. La restauration de frame dans l'adaptateur reste également une
frontière à décomposer. Les primitives natives et les grands entiers gardent
les limites exposées dans le rapport arithmétique.

## Vérifications

La gate complète `scripts/verify.ps1` a réussi sur 310 fichiers Lean et
26 024 constantes, avec aucune exception écrite et 23 fixtures de refus attendu.
Les 166 audits explicites des douze modules de contrôle, les 60 de déduction
et les 48 du programme sont sans axiome. Les sources Lean et les scripts de
contrôle sont restés identiques aux empreintes figées avant cette exécution.
Le relevé conserve une révision d'évidence nulle jusqu'à une nouvelle révision
Git effective ; la réussite est celle de cet arbre de développement vérifié.

Le [contrôle de l'assemblage compilé](../../scripts/check-documentary-assembly-codegen.py)
vérifie les opérations différées, les positions reçues, les captures de l'action
et de la permission à chaque passage, le partage du type, du support, du
stockage, de l'extension, de la sortie et de la frame. Il examine aussi les
corps des constructeurs de connaissance et de frame, puis la fermeture de
progrès qui consomme la sortie. Ses 116 mutations textuelles sont rejetées.
Le contrôle arithmétique ajoute quatre mutations sur les transmissions de la
continuation acceptée : 51 mutations rejetées. Avec les 56 de l'interprète et
les 33 du producteur, le total est de 256.

Ce sont des contrôles de corps C nommés et de champs de fermeture, avec fixtures
textuelles ; ils ne constituent pas une analyse exhaustive du graphe d'appels,
des binaires mutants exécutés ou une borne physique de mémoire.

Le [smoke documentaire](../../scripts/run-documentary-interpreter-smoke.py) vérifie
1 000 verdicts documentaires sur les carburants 0 à 99, 234 verdicts de permission,
72 de position, 32 de ressource et neuf d'intégration : 1 347 verdicts, avec
18 audits runtime sans axiome. Valeurs, origines, événements, traces exactes,
refus et seuils sont comparés à des attentes littérales fixées avant le run.

| Parcours | Seuil exact | Résultat |
| --- | ---: | --- |
| Différence de 43 et 42 | 87 | Valeur 1 et origines [1, 2] |
| Somme de deux occurrences de valeur 1 | 61 | Valeur 2 et origines [1, 2, 1, 2] |
| Règle interdite | 23 | Refus sans lecture des prémisses |
| Citation | 2 | Paquet du maître ; coûts internes encore ouverts |
| Entrée gauche/droite manquante | 3 / 5 | Événement manquant |

La somme échoue à 60 pas et conserve son paquet à 66. Le smoke arithmétique
conserve ses 166 cas et ses 5 312 verdicts de valeur, trace et carburant, avec
sept audits runtime sans axiome. Aucun run supplémentaire de modèle n'a été
lancé ; ces essais restent des vérifications de développement.

## Suite requise

D2 entier reste ouvert : maître de citation, formation des citations,
assemblages de citation et d'entrée manquante, restauration des frames,
appels différés de liaison et justification, composition des continuations,
traces et paquets de l'interprète, modèle complet d'allocation. L'instrumentation
du maître doit conserver son instance et ses productions et rouvrir la
qualification des dépendances concernées au registre.

D3 doit encore borner le bootstrap et protéger les enveloppes des états et
successeurs. D4 doit raccorder le secours effectivement borné aux tours.
CONT-03 et P15 restent ouverts ; les étapes restantes d'A et la phase B
ne sont pas déclarées closes.
