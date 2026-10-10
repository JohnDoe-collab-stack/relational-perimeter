# Producteur documentaire construit sous carburant et conservé dans la formation

Cet incrément poursuit D2 du [plan v0.3](RP_ALIGN_PERSIST_SPEC_v0_3.fr.md)
sur `codex/align-persist-recovery`, depuis
`b6a7529729bf41224f5ad644be520e44b2a41cdd`. Il prolonge les
[lectures de ressources](controle-ressources-documentaires.fr.md).
A conserve la priorité sur B.

Le contrôle construit désormais le producteur binaire de la déduction à
partir des références reçues et des positions effectivement calculées sous
carburant. La formation consomme ce producteur et les deux valeurs déjà lues.
Son témoin conserve le producteur calculé lui-même et la formation antérieure.
L'action entière reste égale à l'action documentaire d'origine.

## Positions et construction payées

[ControlPermission.locatedLookup](../../Tests/LocalAlignment/DocumentaryControlPermission.lean)
retient ensemble la position calculée de la règle et la permission trouvée.
Cette position alimente ensuite la construction du producteur. Elle ne fait
pas l'objet d'un second parcours. Une permission absente arrête la déduction
avant les lectures des prémisses et la construction du producteur.

[ControlProducer.code](../../Tests/LocalAlignment/DocumentaryControlProducer.lean)
calcule les positions des prémisses gauche et droite avec `positionCode`.
`buildCode` consomme ces deux résultats et la position conservée de la règle.
Les ports sont les références typées reçues, dans l'ordre gauche puis droite.
Une égalité de valeurs n'identifie donc pas leurs occurrences ou leurs ports.

| Étiquette | Étapes déclarées | Données construites après paiement |
| --- | ---: | --- |
| `producerKindCell` | 3 | Liste vide, suffixe droit, liste des deux genres |
| `producerPortCell` | 3 | Ports vides, port droit, ports ordonnés complets |
| `producerOutputKind` | 1 | Genre dérivé avec les trois positions calculées |
| `producerAssembly` | 1 | Producteur avec ses ports, son genre et son opération |

Les anciennes étiquettes conservent leurs indices ; les quatre nouvelles
suivent `resourceCell`. Une étape paie l'entrée dans sa continuation différée.
Cette unité compte la sémantique instrumentée ; les allocations et le travail
du runtime ne sont pas tous décomposés par ces huit étiquettes.

Le paquet retourné porte l'égalité avec `Deduction.producer` pour la même
requête et les mêmes références. `buildTrace` construit positivement la trace
des huit étapes, pour tous les résultats de position conformes à leurs
références. `build_bounded` établit la borne `8`. `bounded` et `finite` couvrent
toute requête de la politique reçue et toute paire de références typées :

```text
borne producteur = positionBound gauche + (positionBound droite + 8)
```

La position de règle n'est pas incluse une seconde fois. La borne composée
de `ControlDeduction` ajoute la permission référencée, les deux lectures de
ressources et l'entrée dans la formation. Elle est conservatrice sur le refus,
dont la trace n'entre pas dans les lectures ou le producteur.

## Consommation du producteur effectif

[Deduction.formFromProducerReads](../../Tests/LocalAlignment/DocumentaryDeduction.lean)
reçoit le producteur construit et les valeurs effectivement lues. Il construit
les arguments depuis ces valeurs et appelle une fois l'opération de ce
producteur. Le résultat est conservé dans les nouvelles valeurs du stockage.
`Formation.produced` conserve la formation antérieure et ce même producteur.

Le transport de type aligne les indices de la formation avec ceux de l'action
attendue. Il s'applique au témoin déjà construit ; il ne remplace pas ses
données par un nouveau producteur. `formFromProducerReads_actual` démontre
l'égalité de l'action entière avec `Deduction.form`. `actual_decision` puis
`ControlStep.actual_step` conservent la décision et l'étape d'origine. Le
certificat de contrôle consomme le résultat et la trace réellement obtenus.

La vérification du C a décelé une première écriture dans laquelle une
substitution dans la construction du témoin reconstruisait le producteur.
Cette écriture a été corrigée avant la qualification : seul le type du témoin
est transporté. Le contrôle compilé interdit désormais la reconstruction
d'origine et vérifie le maintien du producteur reçu dans `Formation.produced`.

| Cas du maître | Seuil exact | Résultat conservé |
| --- | ---: | --- |
| Citation | 2 | Même paquet documentaire |
| Différence | 25 | Même valeur et mêmes origines |
| Somme | 35 | Valeur `2`, origines `[1, 2, 1, 2]` |
| Règle interdite | 19 | Refus avant les prémisses et le producteur |
| Prémisse gauche absente | 3 | Même arrêt de liaison |
| Prémisse droite absente | 5 | Même arrêt de liaison |

Les cas Lean de la somme établissent la trace exacte à 35, l'échec à 34 et la
conservation du résultat à 39. Les bornes génériques portent sur les entrées
typées ; les seuils de ce tableau portent sur les cas du maître existant.

## Qualification et portée

Le [client d'exécution](../../scripts/run-documentary-interpreter-smoke.py)
passe **747 verdicts** : 400 documentaires, 234 permissions, 72 positions,
32 lectures de ressources et neuf contrôles d'intégration. Les 18 audits
runtime sont sans axiome. Les attentes littérales couvrent les seuils, les
traces, les valeurs, les identités et les origines, ainsi que le présent,
le reset, l'oubli et le contrôle chargé avec le maître reçu.

Le [contrôle du producteur compilé](../../scripts/check-documentary-producer-codegen.py)
vérifie les huit continuations payées, les ports ordonnés, les trois positions
effectives, les captures distinctes du genre et de l'opération, puis le retour
du producteur assemblé. Le
[contrôle de l'interprète compilé](../../scripts/check-documentary-interpreter-codegen.py)
vérifie son passage à la formation, l'appel unique de son opération avec les
valeurs lues, le maintien du producteur et du prédécesseur dans le témoin, et
la consommation des résultats par les certificats.
Ils rejettent respectivement 31 et 55 mutations textuelles, soit 86. Ces
fixtures vérifient les gardes sur les corps nommés et les captures inspectées
du C du compilateur fixé. Elles ne sont pas des builds de mutants ni une
preuve du graphe complet ou du coût physique.

La gate complète `scripts/verify.ps1` a réussi sur **307 fichiers Lean** :
25 844 constantes dans 306 modules, 364 exceptions générées par le compilateur,
aucun axiome écrit et 23 fixtures de refus conformes. Les 131 audits explicites
des neuf modules de contrôle et les 57 audits du module de déduction sont sans
axiome. Les sources Lean et les scripts du contrôle sont restés inchangés
pendant cette vérification.

Le [relevé de ce passage](controle-producteur-documentaire-verification.json)
consigne les commandes, les résultats et les empreintes des sources, avec
les 186 modules de la fermeture des dépendances locales.
Les relevés précédents restent historiques. Cet incrément ne constitue ni
un audit indépendant ni un nouvel essai confirmatoire de modèle.

Le travail interne de l'opération sur entiers et des autres constructions de
formation reste à instrumenter. Le maître de citation et les assemblages
restent ouverts, comme les coûts de `Code.bind`, des traces et des allocations.
Les calculs de bornes et leur bootstrap restent à borner séparément. D2
entier, D3, D4, CONT-03 et P15 restent ouverts. Cette étape ne clôt ni A ni B.
