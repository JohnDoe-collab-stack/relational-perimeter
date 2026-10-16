# Raccordement de Gödel, du regroupement et de la complétude des réels

## Statut et révision de référence

Ce document est un plan de travail. Il ne vaut ni preuve obtenue, ni nouvelle
affirmation scientifique du dépôt, ni audit extérieur.

Le travail est reparti de `main` au commit exact
`c6711cc790ba5e0bb6bbe777ab89dc265b6d87b9`. La branche
`work/godel-regroupement-raccord` possède désormais le commit de référence
`5492a85c0108a7889e08451f9fab6c9eebf4a082`, qui contient les étapes B à K,
les tests et les passages canoniques. Aucun push n'a été effectué. Le registre
scientifique est préparé dans l'arbre suivant ce commit, avec une révision
d'évidence propre à la nouvelle affirmation afin de ne pas déplacer l'audit
gödelien historique.

### Registre d'exécution du plan

| Verrou | Artefact ou contrôle | État actuel |
| --- | --- | --- |
| B.1 représentation signée et échelles | `RelationalPerimeter/Constitution/Reals/Precision.lean` | construit |
| B.2 égalité exacte | réflexivité, symétrie, transitivité, relèvement exact | construit |
| B.3 proximité | réflexivité, symétrie, affaiblissement, relèvement, invariance et composition | construit |
| B.4 séparation des sources | test d'un relèvement qui conserve la valeur avec des échelles strictement distinctes | construit |
| B.5 audit local | blocs `AXIOM_AUDIT` du module et du test | sans axiome |
| B.6 intégration | `scripts/verify.ps1`, dont `lake build` complet | réussi : 354 jobs, 352 fichiers Lean vérifiés |
| Contrôle de toutes les constantes | audit global compilé | réussi : 30 127 constantes, 351 modules, 510 exceptions générées, 0 exception écrite |
| Contrôle scientifique | `--self-test`, `--static`, `--lean` avec Python 3.12 du runtime de travail | réussi : 20 affirmations, 108 déclarations, dont 88 publiques et 20 de test ; revues déclarées toujours visibles |
| C. tour partagée | journal, six phases, occurrences fraîches et persistance gödelienne | construit ; audit local sans axiome |
| D. ressources exécutées | source/limite, provenance, équivalence relationnelle positive et readout postérieur | construit ; audit local sans axiome |
| E–G. regroupement | chaîne chronologique de profils exécutés, curseur fini ancien-vers-récent, rang exact du nombre restant, forme normale `target`, consommation ordonnée de toutes les charges avec code et `Near`, action cible exacte, préservation, cohérence et non-identification | construit ; audit local sans axiome |
| H. extensions historiques | ajout en fin de sélection, levée des traces locales et de lot, composition, transport des charges et compatibilité exacte de consommation | construit ; audit local sans axiome |
| I. futurs finis | requêtes typées, exécuteur maître familial conservé, requête limite possédant le programme source–regroupement–limite, `Continuation.Exact`, transport bilatéral des admissions et mêmes états, événements et observations normalisés pour deux sources regroupées à profondeur égale | construit ; audit local sans axiome |
| J. raccord terminal | producteur maître universel source–regroupement–limite, aucune exécution parallèle ni rejeu d'un payload formé, spécialisation canonique exacte au premier run, transport des occurrences à travers ses deux requêtes possédées, profondeurs 7 et 13, convergence, readout, `TotalLoop` et restriction d'une fermeture globale cohérente sur les labels antérieurs | construit ; audit local sans axiome |
| K. instance HA | raccord concret sur l'exécution HA existante | construit ; audit local sans axiome |
| Mutations typées | périmètre indépendant, source nue, sortie arbitraire, réponse directe ou rejeu de payload substitué au maître typé, fermeture réduite au premier préfixe et lot non exécuté | rejetées aux sites Lean figés ; 30 fixtures globales validées aux sites exacts |
| Registre scientifique de la nouvelle affirmation | commit de référence, identifiant, empreintes et revues rouvertes | enregistré sur `5492a85c0108a7889e08451f9fab6c9eebf4a082` ; `reader=pending`, `translation=pending`, `independent=not_recorded` |

Le Python 3.9 installé par défaut sur la machine ne peut pas exécuter le
`--self-test`, car il ne connaît pas l'argument `newline` de
`Path.write_text`. Ce défaut d'environnement n'a pas été réparé dans le dépôt :
le même contrôle a été exécuté avec le Python 3.12 fourni par le runtime de
travail. Cette distinction doit rester visible dans toute livraison.

La partie Gödel est déjà intégrée et auditée dans l'architecture courante. Il
ne faut ni restaurer les anciens fichiers supprimés, ni reconstruire une
troisième présentation gödelienne. Les points d'entrée actuels sont :

- `RelationalPerimeter/Constitution/Godel/Diagonal.lean` ;
- `RelationalPerimeter/Constitution/Godel/PerimetralCorrespondence.lean` ;
- `RelationalPerimeter/Instances/HeytingArithmetic/Godel.lean`.

Le plan antérieur devait être corrigé sur trois points décisifs : il citait une
ancienne architecture, il ne construisait pas la tour cohérente des
regroupements finis, et il ne séparait pas assez nettement la complétude
constituée de son readout numérique.

## Cible exacte

La cible n'est pas de déduire les réels du seul `False` de Gödel. Elle est de
construire, sur le **même périmètre produit à partir du même témoin de Gödel**,
deux devenirs qui partagent leur histoire mais jouent des rôles distincts :

```text
témoin diagonal effectivement produit
→ périmètre P, différence, occurrences et provenance
→ continuations positives H₀ ⊂ H₁ ⊂ H₂ ⊂ ⋯
├─ tentative de fermeture dans le même régime
│  → Truth(G) → Proof(G)
│  → contradiction avec la non-prouvabilité du même G
│  → rejet de TotalLoop
└─ actions positives de raffinement et de regroupement
   → obligations finies cohérentes à chaque précision
   → continuation globale déterminée par tous ses futurs finis
   → réel relationnel limite
   → readout dyadique signé de la convergence
```

Le théorème terminal visé est une **complétude séquentielle effective** :
toute famille de réels relationnels munie de données positives de Cauchy et
d'un module explicite produit un réel relationnel limite, avec une preuve de
convergence à toute précision finie. Cette formulation est constructive et ne
place pas le choix d'une limite dans les prémisses.

Le résultat doit comporter deux niveaux, sans les confondre :

1. un niveau constitutif, où la limite est une continuation cohérente produite
   par les actions de regroupement ;
2. un niveau de readout, où les codes dyadiques signés produits par cette
   continuation satisfont la convergence numérique attendue.

Le premier niveau est primitif dans le raccord. Le second est une projection
aval. Le readout ne doit jamais construire rétroactivement la limite, les
occurrences ou leur cohérence.

Cette première cible ne doit pas être renommée « complétude par borne
supérieure ». Un raccord à une formulation d'ordre plus large demanderait un
énoncé et une preuve distincts. De même, la densité, `AC` et `CH` restent des
cibles ultérieures séparées : l'architecture pourra expliquer leur position,
mais la complétude séquentielle ne les prouve pas automatiquement.

### Rôle exact de Gödel dans cette cible

Le témoin de Gödel ne calcule pas les chiffres d'une approximation réelle. Il
construit le périmètre, sa différence et l'obstruction interne qui interdit de
confondre totalité avec fermeture du même régime. Les données dyadiques de la
famille de Cauchy arrivent ensuite comme contextes reçus par la continuation ;
elles sont recherchées, consommées, regroupées et conservées dans cette même
chaîne constitutive.

Le lien recherché est donc causal et architectural : Gödel exclut la mauvaise
forme de totalité, tandis que le regroupement construit positivement la bonne
forme locale-globale. Prétendre dériver les valeurs dyadiques de la seule
non-prouvabilité serait une fausse solution ; placer une construction complète
des réels à côté de `P` sans faire passer ses productions par les occurrences,
actions et extensions de `P` en serait une autre.

## Ce qui est déjà disponible

### 1. Le même témoin gödelien et le rejet de la fermeture

`EffectivelyPresentedSoundGodelSystem` construit une exécution effective.
`ExecutedGodelProduction` enregistre la réception, la diagonalisation, la
production de la phrase et la production du témoin. `ExecutedGodelWitness`
porte ensuite le point fixe, la vérité et la non-prouvabilité du même énoncé.

Pour une exécution `execution`, la seule présentation à conserver est :

```text
P := godelPerimetralPresentation execution
   = godelCircularPresentation execution.witness
```

`GodelAffirmativeConstitution` fournit déjà le tout positif, la continuation
stricte, les occurrences distinctes de production, certification et
continuation, les ressources exactes et leur provenance. La branche négative
est déjà factorisée : une admission de fermeture produit une contraction, puis
`Truth(G) → Proof(G)`, puis `Empty` en consommant la vérité et la
non-prouvabilité du même `G`.

Le raccord réalisé réutilise `executedGodelPerimetralCorrespondence` et ses
données ; il ne copie pas ses conclusions dans une nouvelle interface.

### 2. Une continuation arbitrairement profonde existe déjà

`RelationalPerimeter/Computation/ConstitutiveGeneration.lean` fournit :

```text
H n := ConstitutiveGeneration.iteratedHistory P n
```

`iteratedHistory` itère le producteur libre réel ; ce n'est pas une liste de
sorties supposées. À chaque successeur,
`successorOccurrenceSplit` sépare exactement les anciennes occurrences de
l'unique nouvelle occurrence.

`OccurrencePersistence.lean` et `PerimeterPersistence.lean` fournissent les
transports, injections, distinctions d'occurrences, réalisations finies et
readouts cohérents à profondeur arbitraire. Les lemmes de
`StrongPerimetralTurning.lean` propagent en outre l'obstruction de fermeture le
long de l'histoire engendrée. La tour `H n` est donc la base commune requise ;
il n'est pas nécessaire d'inventer une infinité de périmètres indépendants.

Ici, `n` compte des **opérations constituées**, et non des niveaux de précision.
Cette distinction doit rester visible dans tous les types. Une demande portant
sur le terme `i` d'une famille et la précision `p` consomme une occurrence ; la
production de l'approximation de limite correspondante peut en consommer une
autre. Il serait faux d'identifier automatiquement `H n` au niveau de
précision `n`.

### 3. Le regroupement générique est utilisable

La couche `RelationalPerimeter/Constitution/Grouping` n'est pas liée aux
profils SAT de la machine. Elle fournit déjà :

- `Grouping.Rules`, pour des pas effectifs, énumérés et terminants ;
- `Trace`, `Chain` et la normalisation constructive ;
- `FiniteImage.Target`, `carry` et `carry_fibres` dans `ExactImage.lean`, pour
  l'image produite et ses fibres exactes ;
- `Extension`, pour transporter une opération ancienne vers une trace réelle
  dans le contexte suivant ;
- `AcceptanceAction`, qui sépare l'action sur les charges de sa preuve de
  préservation ;
- `Continuation.Exact` et `FutureContract`, pour comparer exactement tous les
  futurs finis, admissions comprises.

La spécialisation `RoleStatus.History` ne doit pas être utilisée comme raccourci
pour Gödel : ses rôles proviennent de la machine SAT. Le raccord doit instancier
la couche générique depuis `H n`.

### 4. La base numérique doit être construite sans les rationnels du noyau

Un audit direct sous Lean 4.33.1 montre que les lemmes d'ordre nécessaires sur
`Rat` et les ponts de `Dyadic` vers `Rat` dépendent de `propext`,
`Classical.choice` et `Quot.sound`. Ils sont donc incompatibles avec le contrat
d'axiomes du dépôt, même si un nouveau fichier n'invoquait pas explicitement ces
mécanismes.

La base exploitable est l'arithmétique inductive de `Nat`, mais elle doit être
auditée lemme par lemme. Les opérations primitives et plusieurs lois utiles
(`Nat.add_assoc`, `Nat.add_comm`, `Nat.mul_add`, `Nat.pow_succ`, les lois
d'ordre testées) sont sans axiome. En revanche, dans cette toolchain, des
lemmes de commodité comme `Nat.mul_assoc`, `Nat.add_mul` et certaines lois
d'annulation dépendent de `propext`. Une preuve récursive locale de
l'associativité multiplicative a été vérifiée sans axiome ; la même discipline
doit être appliquée à toute loi contaminée nécessaire.

Le raccord devra donc construire son propre code dyadique signé à partir de
naturels et une petite API arithmétique locale auditée. Il ne devra pas
convertir ses preuves vers `Rat`, `Int` ou le `Dyadic` du noyau dans une
déclaration auditée tant que les axiomes de cette conversion ne sont pas nuls.

## Le passage identifié puis réalisé

Un regroupement isolé après un journal fini donné ne suffit pas. La complétude
requiert une famille de regroupements finis dont les résultats restent
compatibles quand une nouvelle requête, une nouvelle occurrence et son niveau
de précision sont constitués.

Le passage qui manquait était donc une **tour graduée de regroupements** :

```text
R operations --E(operations, request)→
  R (operations ++ schedule state request)
       |                         |
 normal operations            normal operations'
       |                         |
 obligation courante   →    obligation étendue
```

Le type de requête publique doit au moins distinguer une demande
d'approximation source `(i, p)` d'une demande de production de limite à la
précision `p`. Une fonction de planification calculable `schedule` décompose
chaque requête admise en une liste non vide d'opérations constitutives, dans
l'ordre du dépôt : réception du contexte, recherche exécutée, action
relationnelle, autorisation et décomposition, continuation effective, puis mise
à jour de la mémoire sous contrat. La préservation reste une preuve séparée
de l'action ; l'observation et le readout viennent après la mémoire et
n'ajoutent pas artificiellement une occurrence.

Le journal `operations` enregistre ces opérations fines, et non seulement les
requêtes publiques. Son histoire sous-jacente est `H operations.length`. Un
étiquetage exact associe chaque opération à l'occurrence qu'elle a
effectivement produite. Ainsi, une requête qui exécute une recherche puis une
action ne peut pas être compressée en une occurrence unique.

Le pas libre de `H` fournit la continuation et l'occurrence ; il ne prétend pas
produire par lui-même le code dyadique. Une structure d'opération exécutée doit
lier dans un seul objet le contexte reçu, la sortie du producteur, l'action qui
la consomme, le pas `generate` réel et l'occurrence fraîche correspondante.
C'est cette structure, et non un simple étiquetage a posteriori, qui sert
ensuite de source au regroupement.

Pour chaque journal fini `operations` :

- `R operations : Grouping.Rules` est construit depuis l'histoire effective
  `H operations.length` et les données de Cauchy effectivement reçues ;
- la normalisation porte les profils sources admis vers les obligations de
  limite déjà demandées et produites ;
- l'action transporte les charges d'approximation ;
- la preuve de préservation certifie séparément le budget de précision ;
- les sources et leurs occurrences restent distinctes, même lorsqu'elles ont
  la même cible opérationnelle ;
- `E operations request` transporte chaque pas ancien vers une trace de
  `R (operations ++ schedule state request)` ;
- une loi supplémentaire prouve que la nouvelle obligation prolonge exactement
  l'ancienne. `Extension.renormalized` sera consommé, mais ne remplace pas
  cette loi de cohérence des approximations.

La totalité globale n'est alors ni un état final parcouru ni l'identification
des extrémités de `P`. Elle est la capacité **prouvée** de répondre à toute
demande de précision finie, avec compatibilité de toutes les réponses déjà
produites. Le plan devra donc fournir séparément l'admission de toute demande de
limite ; le simple fait que `FutureContract.outcome` représente aussi les refus
ne prouve pas cette totalité. Cette totalité par prolongements évite de recréer
`TotalLoop`.

### Enveloppe typée fixe pour la continuation globale

`R operations` et ses cibles sont des types dépendants du journal, tandis que
`FutureContract` exige un seul type `Source`, un seul type `Event` et un seul
type `Observation`. Le plan ne peut donc pas placer directement
`FiniteImage.Target (R operations)` dans `FutureContract.read`.

Le raccord devra construire explicitement :

- un état source fixe sous forme d'une somme dépendante contenant le journal,
  l'histoire exacte et l'état local correspondant ;
- un type fixe de requêtes publiques ;
- un code fixe d'événement normalisé et un code fixe d'observation
  normalisée ;
- une mémoire réduite fixe contenant les obligations déjà produites avec
  leurs précisions ;
- une projection calculable de chaque cible locale vers ces codes fixes ;
- un `Continuation.Exact` prouvant les lois de pas, d'événement, de readout et
  d'admission entre l'exécution riche et cette mémoire réduite.

Avant de remplir `FutureContract`, construire une seule fonction maître
`executeRequest source input`. Sa sortie est un paquet contenant la
planification, la recherche retournée, le code produit, les occurrences et
provenances, l'action exécutée, sa préservation séparée, l'autorisation, la
décomposition, la continuation, la mise à jour de mémoire, l'événement public
et l'état cible. Les champs
`next` et `event` du contrat doivent être des projections de ce même paquet.
Deux fonctions qui recalculeraient indépendamment une valeur égale ne
satisfont pas le partage constitutif demandé.

Les occurrences et provenances riches restent dans l'état source ; elles ne
sont pas effacées par leur code public. `FutureEquivalent` ne sera invoqué
qu'après cette projection exacte vers les types fixes. `Reindexing.lean` ne
résout pas automatiquement ce problème : il demande un
`ExactTypeTransport`, donc une véritable équivalence de types que deux journaux
de longueurs différentes ne possèdent pas en général.

## Données formelles à introduire

Les noms ci-dessous sont des cibles de conception ; leur orthographe pourra
être ajustée avant l'écriture si les types existants l'exigent, sans changer
leur contrat.

### 1. Code dyadique signé et budget de précision concret

Introduire un type exécutable de la forme :

```text
SignedDyadicCode :=
  (positive : Nat, negative : Nat, scale : Nat)
```

Il représente relationnellement
`(positive - negative) / 2^scale`, sans construire une soustraction dans
`Int`, une fraction quotientée ni une valeur `Rat`. Deux codes différents
peuvent présenter la même valeur ; cette pluralité est traitée par une relation,
pas effacée par quotient.

Pour comparer deux codes `x` et `y`, ne pas s'appuyer sur une annulation de
facteur cachée. Un témoin positif `CommonScale x y` fournit une échelle commune
`common`, les deux incréments d'échelle et les égalités :

```text
x.scale + xExtra = common
y.scale + yExtra = common
```

Les composantes positives et négatives sont alors multipliées respectivement
par `2^xExtra` et `2^yExtra`. L'égalité dyadique exacte est l'égalité des deux
différences ainsi relevées, exprimée sans soustraction par une égalité de
sommes de naturels. Pour le témoin d'échelle reçu, noter :

```text
liftedLeft  := x.positive * 2^xExtra + y.negative * 2^yExtra
liftedRight := x.negative * 2^xExtra + y.positive * 2^yExtra
```

Un témoin `Near p x y` doit en plus fournir positivement un
`precisionExtra` tel que `p + precisionExtra = common`, puis les deux
inégalités naturelles :

```text
liftedLeft  ≤ liftedRight + tolerance
liftedRight ≤ liftedLeft  + tolerance
```

où `tolerance = 2^precisionExtra`. La précision annoncée par une réponse doit
garantir que son échelle est assez fine pour construire ce témoin. Les lemmes
à fermer sans axiome sont :

- changement exact d'échelle d'un code ;
- réflexivité et symétrie de `Near` ;
- monotonie quand le budget demandé est relâché ;
- relèvement de deux témoins vers une nouvelle échelle commune ;
- composition de deux `Near (p+1)` en un `Near p` à cette échelle commune,
  sans utiliser une loi d'annulation axiomatique ;
- invariance de `Near` par changement exact d'échelle.

Le partage du budget et tout décalage fini utilisé par la construction
diagonale devront apparaître explicitement dans ces lemmes. Aucun appel aux
lemmes rationnels axiomatiques ne sera admis dans leur fermeture.

`SignedDyadicCode`, `CommonScale` et `Near` sont maintenant conservés dans
`RelationalPerimeter/Constitution/Reals/Precision.lean`. La réflexivité sous
témoin d'échelle, la symétrie, les relèvements exacts et la composition requise
y compilent sans axiome ; le premier verrou n'est donc plus seulement validé
par un prototype.

### 2. Réel relationnel présenté positivement

Un `RelationalReal` ne sera ni un carrier extensif présupposé, ni une classe de
quotient, ni une collection infinie de valeurs matérialisées avant son
effectuation. Sa donnée primitive sera un **producteur calculable** enveloppé
dans un processus d'exécution sur le même `P`. Il contiendra au minimum :

- un programme qui calcule un code uniquement lorsqu'il reçoit une demande de
  précision ;
- un état initial lié à l'histoire courante ;
- une opération calculable qui reçoit une précision et prolonge effectivement
  l'histoire ;
- l'occurrence fraîche, le code dyadique signé et la provenance
  produites par cette opération ;
- la preuve que l'occurrence est exactement celle ajoutée par le prolongement
  consommé, et non une occurrence choisie indépendamment ;
- une preuve positive de cohérence/raffinement entre toutes les réponses
  finies admises.

La fonction d'approximation `Nat → SignedDyadicCode` sera un readout canonique
de ce producteur exécuté. Le code calculé pour une demande ne doit pas dépendre
silencieusement de l'ordre des demandes antérieures. L'état historique peut
changer l'occurrence et la provenance qui portent le code, pas le code annoncé
par le même producteur pour la même demande.

Si une implémentation choisit malgré tout un producteur numérique dépendant de
l'état, elle devra prouver une loi plus forte : deux journaux atteignables qui
diffèrent seulement par l'ordre d'opérations indépendantes donnent des réponses
`Near p` à toute précision demandée. La voie minimale recommandée est de garder
le producteur de code fonctionnel et de réserver la dépendance d'état à
l'effectuation relationnelle.

Pour justifier le mot « réel » sans le poser comme étiquette, cette couche doit
aussi construire l'ancrage dyadique minimal : tout code dyadique signé produit
un processus constant admissible par changements exacts d'échelle, son readout
reste exactement équivalent au code initial à toute précision, et deux codes
reliés par l'égalité croisée donnent des comportements équivalents. La densité
et les opérations de corps ne font pas partie de cette première preuve, mais la
cible doit bien être présentée comme la complétion des codes dyadiques signés,
pas comme un type arbitraire renommé.

Deux processus ne seront pas identifiés par égalité de structure. Il faut
distinguer :

- leur équivalence réelle, obtenue lorsque leurs approximations sont
  relationnellement proches à toute précision ;
- l'équivalence exacte des obligations **après regroupement et
  normalisation**, formulée par `FutureEquivalent` sur les événements et
  observations normalisés.

Exiger l'égalité brute de tous les codes dyadiques serait trop
fort et confondrait un réel avec une présentation particulière. Le readout
numérique brut est donc relié par les bornes de proximité, tandis que le contrat
de futurs compare exactement les obligations opérationnelles regroupées.

L'équivalence réelle devra elle-même porter un module positif. Pour chaque
précision `p`, ce module donne une profondeur à partir de laquelle toutes les
réponses croisées des deux processus sont `Near p`. La transitivité calcule un
nouveau module à partir des deux modules reçus et consomme un cran de budget par
la loi triangulaire. Cette formulation évite à la fois le quotient et une
existence non calculable cachée dans `Prop`.

### 3. Famille de Cauchy exécutable

La donnée d'entrée de la complétude contiendra :

- un processus maître calculable qui reçoit un indice de terme et une
  précision, plutôt qu'une collection de processus indépendants ;
- un module calculable `modulus : Nat → Nat` ;
- une preuve de monotonie du module ;
- pour chaque indice fixé, une preuve de cohérence des réponses en précision,
  ce qui constitue effectivement le terme correspondant de la suite ;
- pour toute précision `p` et tous indices au-delà de `modulus p`, un témoin
  positif, avec son seuil de réponse, que toutes les approximations croisées
  des deux termes sont `Near p` ;
- le raccord de chacun de ces témoins aux occurrences reçues et recherchées,
  et non à de simples codes numériques isolés.

Le module fait partie des données positives requises par un théorème
constructif. Il ne s'agit pas d'un choix ajouté pendant la preuve.

La conclusion de convergence devra retourner le même genre de donnée
positive : pour chaque `p`, un indice de suite calculé et un seuil de réponse
calculé, puis les témoins `Near p` requis. Une simple proposition affirmant
qu'un seuil existe ne suffit pas au contrat du dépôt.

Le processus maître doit aussi prouver que l'exécution d'une requête consomme
exactement la sortie du producteur correspondant à `(indice, précision)`. Il
est interdit de recalculer ensuite une valeur mathématiquement égale pour la
placer dans l'occurrence ou dans le readout.

### 4. Limite diagonale produite

La limite sera construite par un programme diagonal explicite. Pour une
précision `p`, il demande au module un indice suffisamment profond, exécute une
requête source à une précision plus fine fixée, consomme la valeur et le
certificat effectivement retournés, puis exécute la production de
l'approximation de limite. La planification expose les opérations successives
et leurs occurrences distinctes dans la même histoire étendue. Leur nombre
exact doit être reflété par le journal et le rang ; il ne peut pas être
compressé en une occurrence fictive indexée seulement par `p`.

Les lemmes de budget doivent ensuite prouver :

- la cohérence interne des approximations de la limite ;
- la convergence de la famille vers cette limite ;
- l'indépendance du résultat relationnel vis-à-vis des variations de
  présentation qui ont les mêmes futurs finis ;
- l'exactitude du readout dyadique signé.

La limite n'est donc pas un champ reçu dans l'interface de Cauchy. Elle est la
sortie calculée de la chaîne.

### 5. Forme des conclusions terminales

La partie numérique doit aboutir à des fonctions de la forme suivante, et non
à une interface qui recevrait leur résultat :

```text
effectiveLimit :
  ExecutedCauchyFamily P → RelationalReal P

effectiveLimitConverges :
  (family : ExecutedCauchyFamily P) →
  ExecutedConvergence family (effectiveLimit family)
```

`ExecutedConvergence` doit contenir les modules calculés, les témoins `Near` et
les exécutions source et limite. Le paquet terminal renforcé doit en outre
conserver, pour tout journal et toute précision, le programme composé qui
possède les occurrences consommées et la trace d'action correspondante. Il ne
peut pas se réduire à une proposition sur les seuls codes dyadiques.

Le raccord complet doit ensuite construire un résultat de la forme :

```text
godelRelationalRealCompleteness :
  (execution : ExecutedGodelProduction ...) →
  (family : ExecutedCauchyFamily
    (godelPerimetralPresentation execution)) →
  GodelRealCompletenessResult execution family
```

Le résultat contient la limite et sa convergence dérivées, conserve la
correspondance gödelienne déjà obtenue et fournit une fonction séparée qui
transforme toute fermeture globale cohérente en `Empty` par restriction au
premier préfixe. La famille reste une entrée de Cauchy positive ; la limite, la
convergence et le rejet ne le sont pas.

## Ordre constitutif obligatoire de l'implémentation

### Étape A — Geler le socle et les identités

1. Partir du commit de référence indiqué plus haut.
2. Construire une seule fois `execution`, puis `P`.
3. Prouver et réutiliser partout l'identité
   `godelPerimetralPresentation execution =
   godelCircularPresentation execution.witness`.
4. Interdire dans les tests toute seconde présentation indépendante.

### Étape B — Fermer d'abord le noyau dyadique sans axiome

1. Construire `SignedDyadicCode`, `CommonScale`, l'égalité à échelle commune
   et le changement d'échelle.
2. Construire `Near` avec ses témoins positifs de budget.
3. Prouver réflexivité, symétrie, monotonie, relèvement, composition et
   invariance par changement d'échelle en n'utilisant qu'une API de `Nat`
   elle-même auditée ; re-prouver récursivement toute loi de bibliothèque dont
   l'audit n'est pas vide.
4. Auditer chaque déclaration terminale avec `#print axioms`.
5. Arrêter le raccord si un axiome interdit apparaît ; ne pas masquer ce défaut
   par une conversion vers `Rat`, `Int` ou `Dyadic`.

Ce noyau est une dépendance logique de tout le reste. La tour gödelienne peut
être exposée en parallèle dans le raisonnement, mais aucun théorème de
complétude ne doit être annoncé avant la fermeture sans axiome de ce budget.

### Étape C — Exposer la tour d'histoires partagée

1. Définir `H n := ConstitutiveGeneration.iteratedHistory P n`.
2. Prouver que le premier prolongement utilisé est exactement la continuation
   déjà contenue dans `GodelAffirmativeConstitution`, et non un second premier
   pas seulement isomorphe.
3. Définir séparément le type des requêtes publiques, le type des opérations
   constitutives et leur planification calculable.
4. Définir le journal fini d'opérations ; son histoire sous-jacente est
   `H operations.length`.
5. Exposer à chaque ajout d'une opération le transport des anciennes
   occurrences et la nouvelle occurrence exacte.
6. Transporter les occurrences gödeliennes de production et certification
   dans chaque `H n`.
7. Prouver qu'elles restent distinctes de toutes les occurrences de
   continuation ajoutées.
8. Transporter l'obstruction de fermeture jusqu'au terminal de chaque histoire
   sans reconstruire le témoin.

### Étape D — Construire les approximations comme ressources

1. Une demande `(indice source, précision)` ou `(limite, précision)` est reçue
   comme contexte.
2. La recherche exécutée consulte le module de Cauchy et retourne l'indice et
   le certificat requis.
3. La nouvelle approximation est attachée à la nouvelle occurrence de `H`.
4. Sa provenance mentionne l'occurrence source, l'indice recherché et la trace
   qui les relie.
5. Le readout numérique ne doit apparaître qu'après cette production.

Cette étape empêche une fausse solution consistant à poser une suite de codes
dyadiques indépendante puis à la juxtaposer au périmètre de Gödel.

### Étape E — Instancier le regroupement après chaque journal fini

Pour chaque journal fini `operations`, construire une instance réelle de
`Grouping.Rules` :

1. le type d'états est le type **fini des profils effectivement produits dans
   `operations`**, avec leur preuve d'appartenance et leur provenance ; il ne
   contient pas tous les indices naturels encore interrogeables ;
2. les pas sont les actions autorisées par les certificats de proximité ;
3. `choices` énumère exactement les pas autorisés depuis l'état courant ;
4. le rang mesure un travail restant concret ;
5. la décroissance du rang prouve la terminaison ;
6. le diamant prouve la compatibilité des actions locales ;
7. la forme normale contient exactement les obligations de limite déjà
   produites dans `operations`.

Le rang ne doit pas être artificiellement fixé à `1` si plusieurs opérations
sont effectivement consommées. Les `choices` ne doivent pas contenir un pas
vers une sortie préfabriquée.

La réalisation minimale recommandée est déterministe : un état contient un
curseur dans la liste finie des obligations effectivement produites, un pas
consomme la prochaine obligation autorisée, et le rang est la longueur du
suffixe restant. `choices` est alors vide ou singleton ; le diamant découle de
l'unicité du pas depuis un état. Le regroupement n'est pas perdu pour autant :
des profils sources distincts possèdent des états initiaux distincts mais leurs
normalisations atteignent la même obligation de limite produite. Cette
stratégie doit être préférée à un système non déterministe plus large si elle
porte exactement les actions requises.

Cette finitude locale est nécessaire si `FiniteImage.frontier_exact` est
utilisé avec une énumération complète. L'universalité sur tous les indices de
la suite sera obtenue par la capacité de traiter une nouvelle requête et
d'étendre le journal, jamais par une liste finie prétendant contenir tous les
`Nat`. Pour un état local non explicitement fini, seuls `Target`, `carry` et
`carry_fibres` pourront être utilisés ; le théorème de frontière exhaustive ne
sera alors pas applicable.

### Étape F — Séparer action et préservation

Construire une `AcceptanceAction` dont :

- `Payload` contient la charge d'approximation avec ses références typées ;
- `act` exécute le transport le long du pas ;
- `Accept` exprime le budget de précision et la provenance requis ;
- `preserves` prouve séparément que l'action conserve ce contrat.

La sortie de `act` doit être exactement celle dont le readout sera utilisé.
Une seconde reconstruction de la même valeur est interdite.

Prouver ensuite `AcceptanceAction.Coherent` pour les traces qui partent du
même état et rejoignent la même cible. Dans la réalisation déterministe
recommandée, cette preuve doit découler de l'unicité des pas et des traces. La
normalisation d'un journal ne suffit pas à elle seule : la charge transportée
doit également être prouvée indépendante de la trace.

Deux ordres de requêtes publiques donnent en général deux indices
`R operations` différents ; le diamant d'une seule instance de `Rules` ne peut
pas les comparer directement. L'indépendance numérique requise entre ces
ordres provient du producteur fonctionnel commun. Toute invariance
supplémentaire de la mémoire normalisée doit être prouvée dans l'enveloppe fixe
de continuation, après projection, et non attribuée abusivement au diamant
local.

### Étape G — Prouver l'image exacte sans identifier les sources

Utiliser `Grouping.FiniteImage` pour prouver :

- quelles sources atteignent chaque obligation produite ;
- que chaque cible annoncée est effectivement produite ;
- que des sources distinctes peuvent avoir la même obligation future ;
- que cette convergence opérationnelle ne donne aucune égalité entre leurs
  occurrences ni leurs profils.

Le regroupement porte sur le régime d'obligations futures. Il n'efface pas
l'histoire qui a constitué les sources.

L'énoncé universel de convergence ne doit pas prétendre que toutes les sources
de la queue sont simultanément présentes dans une frontière finie. Pour chaque
`i` au-delà du module et chaque précision `p`, la preuve doit calculer
l'extension du journal qui exécute la requête `(i, p)`, puis produire dans ce
contexte étendu la chaîne vers l'obligation de limite déjà construite. La
quantification sur `i` est ainsi une fonction exécutable qui prolonge le même
maître, pas une énumération extensive infinie.

### Étape H — Construire les extensions historiques cohérentes

1. Construire `E operations request` depuis l'inclusion exacte de
   `H operations.length` dans
   `H (operations ++ schedule state request).length` ; l'extension peut donc
   ajouter une trace de plusieurs pas.
2. Lever chaque ancien pas vers une trace réelle ; ne pas le remplacer par une
   égalité de valeurs.
3. Prouver la composition des extensions.
4. Prouver la compatibilité des actions sur les charges.
5. Prouver que l'obligation normale après la requête raffine celle du journal
   antérieur.
6. Prouver que les readouts commutent avec ces transports, après seulement que
   la cohérence constitutive a été obtenue.

### Étape I — Former le contrat de tous les futurs finis

Construire un `FutureContract` où :

- une entrée distingue la demande source `(i, p)` de la production de limite
  à la précision `p` ;
- `Allow` est le certificat positif que la demande peut être traitée depuis
  l'état courant ;
- `next` exécute l'extension et l'action correspondantes ;
- `event` enregistre l'occurrence et la provenance produites ;
- `read` expose l'approximation déjà constituée.

`next` et `event` sont ici les projections de `executeRequest`, pas deux
exécutions concurrentes de la recherche ou du producteur. Les preuves
`nextLaw` et `eventLaw` du pont exact doivent consommer ce paquet commun.

La première ligne décrit l'exécution source riche. Le contrat public utilisera
les codes fixes normalisés définis plus haut ; un `Continuation.Exact` devra
prouver qu'ils sont les projections exactes des événements et readouts riches.
Sans ce pont, `FutureEquivalent` ne serait pas typable sur la famille
dépendante `R operations`.

Prouver d'abord que toute demande de limite est admise depuis tout état
atteignable. Prouver ensuite que la limite construite répond à toute liste
finie de demandes et que deux états regroupés ont exactement les mêmes futurs
autorisés, événements et observations **normalisés**. C'est ici que la totalité
locale-globale est fermée : le global est déterminé par la cohérence de tous les
prolongements finis, pas par une trace exhaustive terminée.

### Étape J — Prouver la complétude et son readout

Le paquet terminal doit fournir simultanément :

- la limite relationnelle effectivement produite ;
- sa tour d'occurrences et de provenances ;
- ses regroupements finis et leurs extensions ;
- la preuve de cohérence de tous les futurs finis ;
- la convergence de la famille de Cauchy vers cette limite ;
- l'énoncé numérique de convergence du readout ;
- la conservation de l'obstruction gödelienne du même `P` ;
- le rejet de toute identification de cette construction avec `TotalLoop`.

Ce dernier rejet doit être une factorisation typée, et non un commentaire. La
continuation globale n'est pas une histoire infinie stockée : c'est un
processus total sur les journaux finis. Il faut donc :

1. définir une tentative de fermeture du processus par son action cohérente
   sur tous les préfixes finis ;
2. prouver un théorème de restriction de cette tentative à chaque préfixe ;
3. la restreindre au premier prolongement, qui est exactement
   `godelPerimetralContinuation execution` ;
4. en dériver, et non en recevoir comme champ,
   `GodelPositiveSameRegimeAdmission execution` ;
5. réutiliser la chaîne existante vers
   `ExecutedGodelProducedCompleteness` et `Empty`.

Le raccord ne doit pas introduire un second `False` indépendant de celui du
même témoin, ni supposer directement l'admission du premier préfixe dans la
définition de la fermeture globale.

La cohérence de cette fermeture n'est pas un adjectif documentaire : son type
conserve le label de toute occurrence antérieure le long de chaque
`DepthExtension`. Une famille arbitraire d'admissions de préfixe sans cette loi
ne constitue pas la tentative globale visée.

Le théorème final ne doit pas recevoir la limite, la convergence ou le rejet
de `TotalLoop` comme champs d'une interface. Ces conclusions doivent être
dérivées des constructions précédentes.

### Étape K — Fermer l'instance concrète

Après le théorème générique, construire le paquet correspondant à
`heytingArithmeticEffectiveGodelSystem`. Cette instance doit réutiliser
l'exécution HA existante et ne contenir aucune hypothèse nouvelle de
correspondance gödelienne.

L'instance HA ne rend pas la complétude dépendante d'une propriété particulière
de HA : elle ferme concrètement le côté gödelien du raccord et prouve que le
paquet complet n'est pas seulement une interface vide.

## Découpage de fichiers réalisé

Le découpage effectivement compilé maintient Gödel hors de
`StrongPerimetralTurning.lean` et sépare les responsabilités suivantes :

1. `RelationalPerimeter/Constitution/Reals/Precision.lean`
   — codes dyadiques signés, changement d'échelle, budget et relation `Near` ;
2. `RelationalPerimeter/Constitution/Reals/ExecutedApproximations.lean`
   — journal des six phases, exécution d'une réponse et readout postérieur ;
3. `RelationalPerimeter/Constitution/Reals/LocalGrouping.lean`
   — profils sources exécutés, action preuve-pertinente et cible exacte ;
4. `RelationalPerimeter/Constitution/Reals/SequentialCompleteness.lean`
   — réel relationnel, famille de Cauchy, limite construite et convergence ;
5. `RelationalPerimeter/Constitution/Reals/HistoricalGrouping.lean` et
   `FiniteGroupingProduction.lean`
   — sélection chronologique, regroupement de lot, consommation exhaustive et
   extensions historiques ;
6. `RelationalPerimeter/Constitution/Reals/ResponseContinuation.lean`
   — pont de bas niveau pour les payloads déjà formés ;
7. `RelationalPerimeter/Constitution/Reals/RelationalEquivalence.lean`
   — équivalence positive des présentations et ancrage des constantes ;
8. `RelationalPerimeter/Constitution/Reals/LimitProduction.lean`
   — producteur complet source–regroupement–limite, maître familial typé et
   futurs finis normalisés ;
9. `RelationalPerimeter/Constitution/Godel/GroupingTower.lean`
   — tour `H n`, occurrences transportées et persistance du même témoin ;
10. `RelationalPerimeter/Constitution/Godel/RelationalCompleteness.lean`
    — paquet terminal partageant le même `P`, branche positive et branche de
    rejet par restriction de la fermeture globale ;
11. `RelationalPerimeter/Instances/HeytingArithmetic/RelationalCompleteness.lean`
    — fermeture de l'instance HA concrète ;
12. `Tests/RelationalRealPrecision.lean`,
    `Tests/GodelGroupingTowerRegression.lean`,
    `Tests/RelationalSequentialCompleteness.lean` et les fixtures négatives
    dédiées sous `Tests/ExpectedFailure/`.

Ce découpage est celui de l'arbre vérifié. Il n'introduit pas d'interface qui
recevrait la limite, la convergence ou le rejet comme conclusion supposée.

## Tests qui doivent faire échouer les fausses solutions

En plus du build et des audits d'axiomes, des tests de mutation ou des exemples
typés négatifs doivent garantir que la preuve ne survit pas si l'on :

- remplace `P` par une présentation indépendante ;
- reconstruit le témoin gödelien au lieu de transporter celui de `execution` ;
- attache les approximations à des occurrences sans preuve qu'elles sont les
  occurrences fraîches de `H` ;
- remplace les extensions historiques par des égalités de readout ;
- rend les règles de regroupement constantes ou leurs cibles préfabriquées ;
- supprime l'action tout en conservant seulement sa preuve de préservation ;
- calcule séparément les sorties de `next` et `event` au lieu de les projeter
  d'un unique `executeRequest` ;
- laisse le code retourné dépendre de l'ordre accidentel des requêtes sans
  preuve de confluence ;
- prouve la confluence des états normaux mais pas la cohérence des charges
  transportées par `AcceptanceAction` ;
- identifie deux sources parce que leurs cibles normales coïncident ;
- reçoit la limite ou la convergence dans l'interface de Cauchy ;
- ne prouve la compatibilité qu'à une profondeur fixée ;
- place directement une cible de type `FiniteImage.Target (R operations)`
  dans le type fixe d'observation du `FutureContract` ;
- utilise une énumération finie comme si elle contenait tous les indices
  naturels futurs ;
- utilise le readout pour reconstruire une occurrence ou une provenance ;
- déduit l'action positive du seul rejet de `TotalLoop` ;
- transforme la continuation globale en fermeture des extrémités de `P`.
- reçoit l'admission du premier préfixe comme champ de la tentative de
  fermeture globale au lieu de la dériver par restriction.

La couverture effectivement réalisée se répartit sans multiplier les
fixtures équivalentes :

| Classe de fausse solution | Contrôle effectif |
| --- | --- |
| présentation indépendante | `IndependentPresentationCannotReplaceGodelPerimeter.lean.fail` |
| source numérique non exécutée | `BareSourceCannotEnterFiniteGrouping.lean.fail` |
| sortie arbitraire ou réponse directe substituée au producteur complet | `ArbitraryGroupingOutputCannotFeedLimit.lean.fail` et `DirectLimitExecutionCannotReplaceMaster.lean.fail` |
| rejeu d'un payload déjà formé substitué au maître typé | `PayloadResponseCannotReplaceTypedMaster.lean.fail` |
| lot annoncé sans consommation de toutes les sources | `SkippedBatchCannotClaimAllSources.lean.fail` |
| premier préfixe substitué à la fermeture globale cohérente | `FirstPrefixCannotReplaceGlobalClosure.lean.fail` |
| occurrence fraîche, persistance du même témoin et obstruction | `GodelGroupingTowerRegression` |
| action réellement consommée, cible exacte et sources non identifiées | `RelationalSequentialCompleteness.groupedAtFourConsumesExecutedSource`, `groupedAtFourConsumesConvergenceWitness`, `executedLimitReadoutIsGroupingAction` et `sharedTargetWithoutIdentifyingSources` |
| ordre chronologique, extension par traces et composition | `finiteBatchGroupingConsumesExactChronology`, `finiteBatchGroupingKeepsChronologicalAppendOrder`, `finiteExtensionRenormalizes` et `twoStepExtensionComposesOnTarget` |
| projections d'un maître unique et futurs normalisés | `twoTypedRequestsProjectionExact`, `retainedMasterLimitAddsTwelve`, `retainedMasterLimitConsumesOwnedSource` et `parallelGroupedSourcesHaveSameFuture` |
| limite construite, convergence et readout postérieur | `effectiveSequentialCompleteness`, `convergesAtEveryPrecision`, `executedLimitProductionReadoutExact` et `completeGodelRaccordUsesCanonicalMaster` |

Les fixtures négatives empêchent les substitutions qui doivent échouer au
niveau des types. Les théorèmes de régression contrôlent les obligations qui
portent sur une donnée positivement construite ; ils ne sont pas remplacés par
des tests d'échec artificiels.

## Obligations documentaires et scientifiques

La réalisation ouvre une affirmation scientifique majeure distincte. Avant
toute intégration dans `main`, les obligations suivantes doivent être
conservées :

1. créer un identifiant propre dans `docs/scientific-claims.json` ;
2. écrire un passage canonique qui annonce exactement la complétude
   séquentielle effective obtenue et ses paramètres ;
3. fournir les références Lean complètes ;
4. garder séparé le statut de la revendication Gödel déjà auditée ;
5. rouvrir les revues rendues nécessaires par les nouveaux passages ;
6. ne pas qualifier de « revue indépendante » une simple compilation ou une
   soumission non lue.

Chaque fichier Lean créé ou modifié devra respecter les interdictions du
dépôt et contenir exactement un bloc `AXIOM_AUDIT` final. Aucun `axiom`,
`sorry`, `noncomputable`, `Classical`, `propext`, `Quot.sound`,
`native_decide` ou `unsafe` n'est admissible.

L'identifiant enregistré pour la nouvelle entrée est
`GODEL_RELATIONAL_SEQUENTIAL_COMPLETENESS`. Ses ancrages sont les sections
« Conclusion formelle du raccord Gödel–regroupement–réels » du passage français
et « Formal Gödel–grouping–real conclusion » de sa traduction anglaise. Ses
références de production couvrent
`effectiveSequentialCompleteness`, `executeFiniteGrouping`,
`executeLimitProduction`, `MasterContinuation.bridge`,
`fullyExecutedSequentialCompleteness`,
`FullyExecutedSequentialCompleteness.groupedSourcesSameMasterFuture`,
`GodelRelationalCompleteness.GlobalSameRegimeClosure`,
`GodelRelationalCompleteness.globalSameRegimeClosureToEmpty`,
`GodelRelationalCompleteness.raccord`,
`GodelRelationalCompleteness.firstLimitProduction_is_canonicalProducer` et
`heytingArithmeticGodelRelationalRaccord`, avec les trois modules de test comme
références de test. Les revues de cette nouvelle entrée commencent à
`reader=pending`, `translation=pending` et `independent=not_recorded`.

Le gel a été effectué seulement après création du commit de référence. Le
schéma 3 permet à la nouvelle entrée de porter sa propre
`evidence_revision`, tandis que les entrées sans surcharge restent attachées à
la révision globale. Ainsi, l'audit indépendant de
`GODEL_INTERNAL_CLOSURE_OBSTRUCTION` demeure exactement sur
`a020dc3267c0670b1316b2b2f8d5b3259ab40d91` : ni son rapport, ni son statut,
ni sa portée n'ont été réétiquetés sur le nouveau raccord.

## Ordre de vérification

1. Compiler chaque nouveau module isolément pendant sa construction.
2. Lire les types complets des théorèmes terminaux, pas seulement leurs noms.
3. Exécuter les tests de partage du même `P`, du même témoin et des mêmes
   occurrences.
4. Exécuter les tests de mutation contre les fausses solutions.
5. Lancer `lake build` sur la branche complète.
6. Vérifier tous les `#print axioms` concernés.
7. Lancer le contrôleur scientifique du dépôt.
8. Relire séparément les passages français et anglais.
9. Inspecter le diff complet et retirer les documents temporaires avant toute
   demande de fusion.
10. Après une fusion explicitement autorisée, refaire le build, les audits et
    les contrôles au commit fusionné.

## Résultat de la revérification du plan

La revérification contre les types actuels du dépôt conduit au verdict
suivant : la voie reste réalisable, mais seulement avec les corrections
intégrées dans cette version.

| Point contrôlé | Verdict du plan |
| --- | --- |
| Même exécution, même témoin et même `P` | Imposé |
| Premier prolongement identique à la continuation gödelienne existante | Imposé |
| Profondeur d'histoire distincte de la précision | Corrigé |
| Plusieurs opérations par requête et occurrences distinctes | Corrigé |
| Types fixes requis par `FutureContract` | Couvert par l'enveloppe et le pont exact |
| Finitude locale distincte de l'universalité sur `Nat` | Corrigé |
| Indépendance numérique vis-à-vis de l'ordre antérieur des requêtes | Satisfaite par le producteur de code fonctionnel ; l'histoire et la provenance restent ordonnées |
| Action distincte de sa préservation | Conservé |
| Regroupement sans identification des sources | Conservé |
| `Rat`/`Dyadic` du noyau compatibles avec l'audit | Non ; retirés du chemin de preuve |
| Noyau dyadique signé fondé sur `Nat` | Chemin constructif retenu |
| Fermeture globale vers le même `False` de Gödel | Par restriction dérivée au premier préfixe |
| Limite ou convergence cachée dans les prémisses | Interdit |

Les risques techniques qui conditionnaient ce plan sont maintenant
fermés dans l'arbre de travail : le calcul dyadique signé et les lois de
composition de `Near` sont constructifs et sans axiome ; la famille d'états
locaux commute avec l'enveloppe fixe de continuation. En particulier, le code
retourné par l'action de regroupement est consommé par une réponse exécutée,
et deux sources produites à profondeurs égales donnent la même projection puis
les mêmes futurs finis normalisés sous l'exécuteur maître familial conservé,
sans identification de leurs journaux ni de leurs identités. Une requête limite
du contrat typé possède désormais le `ExecutedLimitProduction` complet ; un
simple rejeu du payload formé n'a pas le type de ce maître. Une chaîne
`ExecutedSourceChain` relie en outre chaque
exécution à la fin exacte de la précédente ; sa sélection dérivée est parcourue
de la plus ancienne source à la plus récente par un curseur de rang égal au
nombre de charges restantes. `executeFiniteGrouping` consomme exactement toute
la sélection, et l'extension historique transporte aussi ces règles de lot et
leurs charges, sans reconstruire leurs sorties.

## Critère de réussite

Le raccord est réussi seulement si l'on peut suivre, dans les types et dans les
preuves, la même chaîne constitutive issue de `P`, le transport du témoin et de
son obstruction dans tous ses préfixes, puis la consommation des ressources de
Cauchy reçues dans chaque occurrence, chaque action de regroupement et le réel
limite, tout en gardant les distinctions suivantes :

- le rejet de la fermeture n'est pas la construction de la limite ;
- le regroupement des obligations n'est pas l'identification des sources ;
- la totalité globale est la cohérence de tous les futurs finis, pas une boucle
  terminale ;
- la complétude est produite avant d'être lue extensivement ;
- le readout numérique conserve la construction mais ne la constitue pas.

Cette chaîne est maintenant construite jusqu'au paquet terminal et à l'instance
HA, puis enregistrée contre son commit de référence avec ses empreintes et ses
revues ouvertes. La gate intégrale réussit sur cet état enregistré. Aucun
statut d'audit indépendant n'est transféré de la preuve de Gödel antérieure
vers ce nouveau raccord. Il ne reste que le commit local final avant toute
éventuelle demande d'intégration.
