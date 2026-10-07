# Revue des corrections de la chaîne constitutive

## Décision et invariants

Cette correction répond au rapport sur le commit
`b32946c708393fc3574bd492edc32d5022a0cfec`. Elle est réalisée sur la branche
isolée `codex/constitutive-chain-scientific-audit-20261007`, depuis
`81f67adfaa239e1af606c82233ca91ce314dab95`.
L'utilisateur a demandé ces corrections puis autorisé deux commits locaux :
les sources corrigées, puis leur registre. Aucun push ni nouvel audit n'est
autorisé dans ce lot.

La clarification des paragraphes trois et quatre de la conclusion est
explicite : le résultat caractérise la **pleine largeur `2^n`**, non toute
croissance exponentielle. Les paragraphes un et deux restent inchangés.
Les énoncés Lean acquis, les contrats, les quatre fichiers primitifs,
les figures et le comportement des définitions exécutables sont conservés.
Les protocoles et reçus d'audits précédents restent historiques ; aucun
verdict ancien n'est attribué à ces sources corrigées.

## Pleine largeur et regroupement effectif

La [conclusion canonique](../conclusion-largeur-exponentielle-conservation-identites.fr.md)
dit désormais explicitement que la largeur opérationnelle égale `2^n`
si et seulement si `carry` est injective, pour les régimes surjectifs de
la classe binaire formalisée.

La non-injectivité seule ne suffit pas à éliminer une croissance exponentielle.
`UnifiedMaster.PolicySpectrum.half_width` construit précisément le cas
`2^(n-1)`. La largeur un du régime exécuté vient de la convergence des
cibles produites et de leur image exacte. Ni ce théorème, ni les preuves
de distinction des profils, ni le spectre partiel ne sont modifiés.

## Initialisation universelle du maître

[MasterRuntime](../../RelationalPerimeter/Computation/Machine/MasterRuntime.lean)
expose `receive_exact`, `receive_core_exact` et `receive_problem_exact`.
Ils quantifient sur tout `input`, tout scope, toute formule et tous les
contextes reçus. Le premier épingle la mémoire entière à la projection du
maître public correspondant ; les deux autres exposent ses composantes.
Ils ne prouvent pas l'atteignabilité canonique des contextes reçus.

[MasterIntegration](../../Tests/Machine/MasterIntegration.lean) ajoute trois
régressions universelles, sans supprimer l'exemple d'indice zéro ni les cas
SAT à une et deux branches. Un client compilé avec le seul import public
`RelationalPerimeter` résout les trois preuves sans axiome.
Le contrôle compilé de l'appel unique au maître reste séparé de ces égalités.

## Routage sans recherche supplémentaire

[Le contrôleur compilé](../../scripts/check-integrated-machine-codegen.py)
suit désormais `FrontierCircuit.fire`, `Routing.apply` et `routeProblem`,
leurs helpers transitifs et les cibles de fermetures statiques. Il contrôle
la propriété de l'artefact qui définit chaque fonction, pas seulement son nom.
Une dépendance extérieure au circuit et aux interfaces de routage est refusée.
Les callbacks `lean_apply_*` et les corps projet manquants sont aussi refusés.
La longueur de liste est une frontière explicite de la bibliothèque Lean.

Onze auto-tests protègent les trois entrées, les helpers, les fermetures,
les callbacks et les corps manquants. Ils exigent le motif de rejet attendu.
Le code livré est accepté ; une panne étrangère ne compte pas comme rejet.

Le contournement M13b a été reproduit hors du dépôt en remplaçant, dans
`Routing.apply`, `some (output.slot, output.bits)` par :

```lean
some (output.slot + (VariableMaster.openFrontier [] slot []).frontier.length, output.bits)
```

Ce module mutant compile avec le même setup Lean. Le C appelle réellement
`VariableMaster.openFrontier` et lit sa frontière. Le contrôle limité à
`fire` l'accepte encore ; le nouveau contrôle le rejette pour la dépendance
transitive à `AcceptedFrontierPreservation.c`, depuis `Routing.apply`.
La production du dépôt n'a pas été modifiée pour ce contrôle.

Cette vérification locale n'est pas une mesure de coût confirmatoire.
Le probe V1 exigeait à tort que le premier diagnostic soit un nom interdit ;
il a échoué car le contrôleur rejette d'abord l'artefact SAT atteint.
Le probe V2, figé avant sa propre exécution, exige exactement ce diagnostic.
Les deux sorties sont conservées séparément hors du dépôt.

| Élément du contrôle local V2 | SHA-256 |
| --- | --- |
| Source Lean mutante | `38ebc93e35444c4950d3a6e4323367b588e2be7e26acdebc0879d161cbcdbd74` |
| C mutant généré | `57c46c8e1bfc19f2c657c4a5e391325816105b9c69193cf8ab6679303a964e49` |
| Probe V2 | `46e257c866a57e63fa8cc81867d66264ac449dc03ae013a2565cdc4ee7f62f45` |

## Contrôles locaux et statut

Les builds `lake build +RelationalPerimeter` et `lake build` passent,
respectivement 201 et 246 jobs, sans avertissement Lean. Les six nouvelles
preuves et le client public ne dépendent d'aucun axiome.
Le contrôle intégré du code compilé passe, y compris les nouveaux auto-tests.

Les contrôles documentaires complets exigent ensuite un vrai commit de
référence contenant ces sources. Le second commit actualise les ancrages,
les empreintes des dépendances et les références aux nouvelles preuves.
Les revues de lecteur et de traduction restent `pending`, et l'avis
indépendant `not_recorded`. Un registre frais n'est pas un verdict scientifique.
Les deux vérificateurs complets doivent être exécutés sur cet état figé.

Les textes français et anglais distinguent aussi les trois frontières
signalées par l'audit : le témoin trouvé agit dans l'évaluation et la
préservation, alors que les gates lisent les constructeurs du code ; le
partage compilé peut bénéficier du compilateur ; la confidentialité d'un
constructeur ne remplace pas une impossibilité de forge par les types.
La stratification, l'identité des sources et les domaines des contrats
ne sont pas remplacés par ces contrôles d'implémentation.
