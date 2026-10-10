# Lectures de ressources payées et formation depuis leurs résultats

Ce document conserve les résultats du passage consacré aux lectures de
ressources. Le [passage suivant](controle-producteur-documentaire.fr.md)
ouvre la construction du producteur et conserve sa valeur effectivement
calculée dans la formation. Les seuils et appels ci-dessous décrivent le
passage historique ; son relevé garde ses empreintes d'origine.

Cet incrément poursuit D2 du [plan v0.3](RP_ALIGN_PERSIST_SPEC_v0_3.fr.md),
sur `codex/align-persist-recovery`, depuis
`b6a7529729bf41224f5ad644be520e44b2a41cdd`. Il prolonge le
[contrôle des permissions](controle-permissions-documentaires.fr.md).
A conserve la priorité sur B.

La déduction lit maintenant ses deux prémisses sous contrôle du carburant.
Elle transmet les valeurs effectivement lues à l'opération de la règle reçue,
puis conserve la formation positive du même producteur. Elle ne relance pas
la lecture d'origine pour former son résultat. Une permission absente produit
le refus avant toute lecture de prémisse.

## Parcours et borne des lectures

[DocumentaryControlResources](../../Tests/LocalAlignment/DocumentaryControlResources.lean)
parcourt les valeurs du stockage reçu et la référence typée reçue. Chaque
cellule visitée coûte une transition `resourceCell`. La continuation est
différée jusqu'au paiement : à `.here`, elle rend la valeur de cette cellule ;
à `.prior`, elle poursuit avec le suffixe effectif et la référence précédente.

Le résultat contient son égalité avec `Resources.read` sur ces mêmes entrées.
`readTrace` construit une trace exécutable pour toute famille de valeurs typées
et toute référence. `read_bounded` et `read_within` établissent la réussite au
coût `ref.position + 1`. `read_short` établit l'échec avec tout carburant
inférieur à ce seuil exact. Deux valeurs égales situées à des occurrences
différentes conservent leurs références et leurs coûts de parcours distincts.

## Une formation qui consomme les résultats

[DocumentaryDeduction.formFromReads](../../Tests/LocalAlignment/DocumentaryDeduction.lean)
reçoit les deux valeurs et leurs égalités de lecture. Il calcule une fois
`evaluate` depuis ces valeurs. Le nouveau stockage retient ce résultat et
les anciennes valeurs ; son témoin est `Formation.produced`, avec la formation
antérieure et `Deduction.producer request leftRef rightRef`.

Les égalités alignent les indices de ce témoin et sont effacées à l'exécution.
Elles ne remplacent pas la formation par un stockage déclaré donné.
`formFromReads_actual` établit l'égalité de l'action entière avec `Deduction.form`
sur le même savoir, la même règle et les mêmes références. Le producteur,
ses ports et les obligations de justification restent ceux du maître existant.

[DocumentaryControlDeduction](../../Tests/LocalAlignment/DocumentaryControlDeduction.lean)
compose la permission, la lecture gauche, la lecture droite et l'entrée payée
dans cette formation. `actual_decision` conserve l'égalité avec la décision
d'origine. `bounded` majore les transitions déclarées depuis les entrées :
borne de permission référencée, puis coût gauche, coût droit et une transition
de formation. Cette majoration inclut les lectures même dans le cas du refus ;
la trace effective du refus s'arrête avant elles.

L'assemblage documentaire et son certificat consomment toujours la décision
effectivement obtenue. La somme garde la valeur `2` et les origines
`[1, 2, 1, 2]`, établies par les témoins de complétude du programme reçu.

| Cas du maître | Seuil exact actuel | Changement |
| --- | ---: | --- |
| Citation | 2 | Frontière inchangée |
| Différence | 13 | Deux visites à gauche et une à droite |
| Somme | 21 | Deux visites pour chacune des deux lectures |
| Règle interdite | 19 | Aucune lecture de prémisse |
| Prémisse gauche absente | 3 | Arrêt après la liaison absente |
| Prémisse droite absente | 5 | Arrêt après la liaison droite absente |

## Contrôles et frontières restantes

Le [client d'exécution](../../scripts/run-documentary-interpreter-smoke.py)
passe **587 verdicts** : 240 documentaires, 234 permissions, 72 positions,
32 lectures de ressources et neuf contrôles d'intégration. Ses 18 audits
sont sans axiome. Les attentes sont littérales ; les lectures couvrent des
valeurs répétées à des occurrences distinctes, une valeur négative et un
entier au-delà de la taille native. Les étapes documentaires vérifient aussi
les refus, les origines, la demande incorrecte, le reset et l'oubli.

Le [contrôle du C produit](../../scripts/check-documentary-interpreter-codegen.py)
vérifie le paiement différé, les références reçues, la transmission des deux
résultats à la formation et à l'opération, le stockage du résultat calculé
et le maintien du témoin positif avec son prédécesseur et son producteur.
Il interdit les appels de relecture et de reconstruction d'origine dans ces
corps, y compris les fonctions d'accès aux supports et aux arguments du
producteur. Il rejette 50 mutations textuelles. Sa portée reste celle des corps
nommés et des captures de continuations inspectées sous le compilateur fixé.

La gate complète `scripts/verify.ps1` a réussi sur **306 fichiers Lean** :
25 806 constantes dans 305 modules, 364 exceptions générées par le compilateur,
aucun axiome écrit et 23 fixtures de refus conformes. Les 120 audits explicites
des huit modules de contrôle et les 55 audits du module de déduction sont sans
axiome. Les sources Lean sont restées inchangées pendant cette vérification.

Le [relevé de ce passage](controle-ressources-documentaires-verification.json)
consigne les résultats, les commandes, les empreintes et les 185 modules de
la fermeture des dépendances locales.
Les relevés antérieurs restent historiques. Aucun audit indépendant ou nouvel
essai confirmatoire de modèle n'est attribué à cet incrément.

La transition `deductionProducer` compte encore une invocation contenant
l'opération entière sur les entiers, la construction du producteur et la
construction de la formation. Leur travail interne reste à instrumenter,
comme le maître de citation, les assemblages, `Code.bind`, les traces et les
allocations. Le calcul des bornes reste une obligation du bootstrap D3.
D2 entier, D3, D4, CONT-03 et P15 restent ouverts à ces frontières.
