# Aristotle — audit scientifique adversarial indépendant

## 1. Mission et révision immuable

Audite le projet ci-dessous, son résultat scientifique complet et le raccord nouvellement ajouté. Ne cherche ni à confirmer le résultat par complaisance, ni à le réfuter en lui substituant une exigence différente. Chaque verdict doit être justifié par des déclarations, leurs dépendances et des essais reproductibles.

**Ne corrige pas le checkout cible.** Travaille sur une copie propre figée ; place les sondes, mutations, correctifs de sondes et résultats dans des copies jetables séparées. Ne pousse rien et ne fusionne rien. Les commentaires, noms de théorèmes, certificats, rapports précédents et ce prompt ne constituent pas des preuves.

```text
repository: https://github.com/JohnDoe-collab-stack/relational-perimeter.git
branch: chatgpt/endogenous-width-proof-20260929
scientific_target_commit: 1ca8e89ed02eacc71eb70efa1ccab84985fb8ace
scientific_target_tree: 9379b85f008b7618ca3336a4a2c8e7730edd3681
immediate_parent: ded0e8ef4d343c091b66c80010c5a6827a589319
parent_of_immediate_parent: ea3f26c20267cba42059e2f0d47bfe7e9244ee96
original_protocol_target_for_comparison_only: 5617ab4b09e5c0c044645737acd62973457b9a59
main_observed_at_preparation: 8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685
merge_base_target_with_that_main: 8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685
required_toolchain: leanprover/lean4:v4.33.1
observed_lean_commit: 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
```

La branche de livraison contient aussi un commit de préparation d'audit, postérieur au commit scientifique. **La cible est le SHA scientifique ci-dessus, pas le HEAD mobile de la branche.** Les fichiers sous `audit/aristotle-20260929/` constituent du matériel de préparation ; ne les confonds pas avec le code au SHA cible. Vérifie leur provenance avant de les exploiter.

Clone le dépôt toi-même et enregistre les révisions avant/après. Une absence ou une divergence du commit cible, de son parent ou de son arbre est un blocage d'identité : rapporte-la, ne choisis pas une autre version. `main_observed_at_preparation` est une référence historique vérifiée lors de la préparation ; si le `main` distant a avancé, relève les deux valeurs sans changer la cible.

Commandes initiales, dans un répertoire temporaire neuf :

```bash
set -euo pipefail
TARGET=1ca8e89ed02eacc71eb70efa1ccab84985fb8ace
PARENT=ded0e8ef4d343c091b66c80010c5a6827a589319
MAIN_REF=8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685
BRANCH=chatgpt/endogenous-width-proof-20260929
WORKSPACE="$(mktemp -d)"
git clone https://github.com/JohnDoe-collab-stack/relational-perimeter.git "$WORKSPACE/target"
cd "$WORKSPACE/target"
git fetch origin "$BRANCH"
DELIVERY_HEAD="$(git rev-parse FETCH_HEAD)"
git merge-base --is-ancestor "$TARGET" "$DELIVERY_HEAD"
git checkout --detach "$TARGET"
test "$(git rev-parse HEAD)" = "$TARGET"
test "$(git rev-parse HEAD^)" = "$PARENT"
test "$(git rev-parse HEAD^{tree})" = 9379b85f008b7618ca3336a4a2c8e7730edd3681
test "$(git rev-parse "$PARENT^")" = ea3f26c20267cba42059e2f0d47bfe7e9244ee96
test "$(git merge-base "$TARGET" "$MAIN_REF")" = "$MAIN_REF"
test -z "$(git status --porcelain)"
git ls-remote origin refs/heads/main "refs/heads/$BRANCH"
mkdir -p "$WORKSPACE/audit/$TARGET"
```

Le dossier de rapport `audit/<TARGET>/` est extérieur au checkout immuable. Fais un inventaire des sources suivies, de leurs SHA-256 et des imports avant les vérifications ; compare-le à la fin. Ne copie pas des `.olean` d'une autre révision pour simuler une compilation propre.

**Environnement Aristotle.** Indique les capacités effectivement disponibles : checkout complet, shell, Git, version Lean, Lake et PowerShell. Si le service ne fournit qu'une interface de preuve ou ne supporte pas le compilateur épinglé, rapporte précisément les contrôles non exécutés. Ne remplace pas silencieusement Lean, les définitions ou les dépendances ; n'ajoute pas Mathlib pour contourner une difficulté. Un travail effectué dans un autre environnement doit être recontrôlé dans celui du dépôt avant de compter comme vérifié. Ne simule aucune sortie de commande.

## 2. Cible scientifique inchangée

La cible est le texte suivant, intégralement. N'en change ni les objets, ni les quantificateurs, ni la direction des dépendances pour faciliter l'audit.

> **Dans ce cadre, la constitution relationnelle des dépendances est primitive. Le calcul produit lui-même, pendant son exécution et à partir de ce qu'il a déjà produit, sa décomposition opérationnelle et détermine ainsi quelles alternatives doivent continuer à être traitées comme des obligations indépendantes.**
>
> **Cette exécution ne produit pas d'explosion exponentielle de la largeur opérationnelle : bien que le déploiement extensif des profils constitués ait une largeur 2^n, le régime exécuté les regroupe en une seule obligation sans identifier les profils eux-mêmes.**
>
> **Dans la classe binaire formalisée, une largeur opérationnelle exponentielle apparaît si et seulement si le régime impose de conserver séparément toute la multiplicité extensive, c'est-à-dire si son application `carry` est injective.**
>
> **L'explosion exponentielle de la largeur opérationnelle est donc démontrée ici comme l'effet exact de cette exigence extensive de conservation indépendante, et non comme une conséquence nécessaire de la structure relationnelle du problème elle-même.**

La portée fixée dans les documents est la **pleine largeur exactement `2^n`**, pas l'ensemble des fonctions asymptotiquement exponentielles. Pour l'instance publique positive, `n = input + 1` ; pour la classe générale, `n = stageCount`. Vérifie cette différence de paramétrage et ne remplace pas un quantificateur général par quelques exemples.

Le théorème d'équivalence doit valoir pour chaque membre de la classe binaire et chaque régime surjectif concerné. L'exécution endogène particulière de largeur un est instanciée sur la famille SAT engendrée du dépôt ; n'attribue pas cette exécution à tous les membres abstraits de la classe. Aucun résultat `P = NP`, `P ≠ NP`, aucune borne universelle de temps/mémoire ou propriété de tout arbre adaptatif ne doit être inféré.

Sépare dans ton analyse : (i) la validité des théorèmes Lean, (ii) leur adéquation à chaque phrase française, (iii) les exigences adversariales fortes A–J. Une mutation survivante peut révéler une redondance ou un défaut du contrat sans réfuter un théorème mathématique existant. Inversement, les bons nombres ne suffisent pas à établir la production constitutive revendiquée. Cette séparation analytique ne dispense d'aucun contrôle obligatoire et ne permet pas un verdict global positif si un contrôle reste non vérifié.

## 3. Lecture préalable et méthode à respecter

Lis intégralement les documents avant de conclure, puis les modules concernés et leurs dépendances nécessaires. Respecte l'ordre interne, les distinctions, les hypothèses et les limites de chaque fichier. Tiens un relevé des fichiers et plages lus ; ne déclare pas une lecture exhaustive à partir d'extraits.

Entrées documentaires au commit cible :

1. `README.md` et `docs/relations-primitives-constitution-perimetre.fr.md` ;
2. `docs/decomposition-operationnelle-endogene.fr.md` ;
3. `docs/conclusion-largeur-exponentielle-conservation-identites.fr.md` ;
4. `docs/positionnement-et-portee.fr.md` ;
5. les versions anglaises correspondantes, lorsqu'elles ajoutent une assertion ou diffèrent ; les figures citées si leur contenu est nécessaire à l'interprétation.

L'ordre constitutif à vérifier est :

```text
relations typées primitives de formation, provenance, source et cible
→ témoins positifs
→ occurrences de rôle constituées
→ histoires dépendantes de ces occurrences
→ profils et frontière source dérivés de cette constitution
→ transformation exécutée sur ces mêmes profils
→ codétermination produite par élimination de la chaîne exécutée
→ régime représentant exactement son image, avec admission justifiée
→ lectures de largeur et équivalence exponentielle
```

La lecture extensive ne constitue pas ses propres objets. Une sélection de positions n'est pas une occurrence réalisée par simple changement de nom. L'action totale n'est pas sa preuve de préservation ; un transport dirigé n'est pas une équivalence ; absorption n'est ni identification ni impossibilité ; image exacte et admission ne sont pas identiques ; provenance causale et nouveauté informationnelle ne sont pas synonymes.

### Entrées de code : réutilisation à vérifier, non conclusion imposée

La production endogène possède déjà des constructions dans le dépôt. Ne la présume pas absente parce que le nouveau pont n'en redémontre pas tout le contenu. Examine leurs termes et leur réutilisation effective, sans prendre leur existence déclarée comme un verdict.

Sous `RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/` :

- `ConstitutiveInterface.lean`, `ConstitutiveFullStep.lean`, `ConstitutiveFeedback.lean` : génération, découverte exécutée, transformation, échec, état transmis et feedback ;
- `ExecutedOperationalReduction.lean` et `ExecutedOperationalReductionHistory.lean` : ouverture, statut, absorption autorisée, préservation et lectures transitoires ;
- `InstrumentedExecutionRealization.lean`, `CausalOperationalExecution.lean`, `PrefixLocalOperationalProduction.lean` : source faisant autorité, production locale et suites dépendantes ;
- `RelationalConstitutiveRoles.lean`, `RoleIndexedProfiles.lean`, `RoleIndexedProgram.lean`, `ExecutedRoleIndexedReduction.lean` : constitution, réalisation, action et traces ;
- `RoleProfileSemantics.lean` et `ExecutedCausalNormalization.lean` : action sur données arbitraires, critères, autorisation et image ;
- **`ExecutedFeedbackBridge.lean`** : `StepFacts`, `stepFacts`, `producedRoleAction_is_discovered`, `Along`, `along`, `widthTrace_existing`, `widthTrace_le_two`, `public_along` ;
- **`ConstitutiveExtensiveSeparation.lean`** : `EndogenousDecompositionAndWidth`, `endogenousDecompositionAndWidth`, `binaryClass_fullWidthExactlyInjective`, `extensiveMultiplicity_doesNotForceFullOperationalWidth`.

Autres points indispensables : `SemanticImage.lean`, `RelationalProfileConstitution.lean`, `RelationalRoleExtensiveFamily.lean`, `FiniteExtensiveAddressing.lean`, la façade `RelationalPerimeter/Computation/EndogenousOperationalDecomposition.lean`, la racine `RelationalPerimeter.lean` et les tests clients.

Le point d'entrée annoncé du nouveau raccord est :

```lean
RelationalPerimeter.Computation.EndogenousOperationalDecomposition.endogenous_production_and_width_separation
```

Déplie intégralement son type `EndogenousDecompositionAndWidth`, chaque champ et chaque prédicat référencé. Vérifie que sa preuve assemble des résultats réellement raccordés aux mêmes données, pas des certificats indépendants simplement juxtaposés. Vérifie notamment que `Along` porte sur les têtes de l'exécution qui définit le porteur public, et que l'action du rôle est l'action découverte sur toute continuation.

Les tests à examiner incluent `Tests/EndogenousWidthBridgeRegression.lean`, `Tests/ConstitutiveObjectiveRegression.lean`, `Tests/RelationalExtensiveIffRegression.lean`, `Tests/SemanticImageRegression.lean` et les régressions de stabilité opérationnelle. Leur succès ne remplace pas l'audit des définitions.

## 4. Contrôles obligatoires A–J

### A. Primitivité de la constitution relationnelle

Vérifie la constitution effective du porteur et la fonction de chacun des quatre accords dans les constructions qui l'utilisent. Stocker un témoin à côté de données déjà suffisantes ne suffit pas. Localise le producteur, le consommateur, l'index dépendant et les voies de récupération de chaque accord.

Mutations obligatoires : remplacer les quatre familles par `Unit` ; retirer les témoins un par un ; conserver les témoins mais les ignorer ; remplacer les occurrences constituées par le porteur brut. Poursuis les essais jusque dans leurs conséquences publiques, sans changer silencieusement le sens des conclusions.

Distingue deux opérations : effacer une copie aval en récupérant le même accord depuis un rôle riche, et effacer aussi l'origine constitutive de cet accord. Consigne les deux. La survie de la première n'est pas une preuve d'absence de toute relation ; elle reste un problème pour l'exigence forte d'indispensabilité de cette interface. Ne transforme pas cette distinction en exemption de test. Si les mêmes conclusions survivent à la mutation obligatoire, ne marque pas A `VERIFIED` sans expliquer exactement ce qui a été supprimé et ce qui reste.

### B. Un porteur public faisant autorité

Vérifie définitionnellement que le porteur de l'histoire exécutée, celui du régime et celui de l'application publique du théorème binaire sont le même. Ajoute le domaine de `imageDescription` et celui de l'action sémantique à cette vérification.

Une égalité propositionnelle, `HEq`, un cast, un adaptateur ou une copie reconstruite ne remplit pas ce contrôle. Cela n'interdit pas les transports internes de réalisation prévus par la méthode : vérifie leur rôle sans les confondre avec un second porteur scientifique.

### C. Production endogène, locale au préfixe

Lis le corps de `executeCausalOperationalHead`, celui de l'exécuteur récursif et le raccord à la découverte existante. Vérifie que la tête est produite depuis la source, que la suite dépend de son état et de son contexte produits, et que la provenance/graine utilisées ensuite viennent effectivement de cette production.

Contrôle les preuves existantes `nextDiscoveryConsumesProducedProvenance`, `nextDiscoveryConsumesRetainedSearchSeed`, l'exclusion des étapes après échec et la non-factorisation sur le domaine comparateur défini. Ne confonds pas états comparateurs contrefactuels et états émis par l'exécution de référence.

Vérifie le rôle exact des équations de tête, du théorème d'indépendance de l'horizon et de `ExecutedFeedback.Along`. Une égalité de résultat ne prouve pas à elle seule un ordre d'évaluation ; distingue inspection de la définition, dépendance typée, propriété extensionnelle et propriété du calcul exécuté.

Tente une mutation cohérente calculant/stockant la tête à partir d'une histoire future achevée, puis une suite repartant d'un état racine ou d'un contexte indépendant. Le rejet demandé pour la première doit provenir de la dépendance de production, pas seulement de la confidentialité d'un constructeur ou de l'unicité du résultat. Si une variante extensionnellement équivalente passe, indique exactement quelle prétention forte elle invalide ; ne prétends pas qu'elle réfute l'existence de l'exécution de référence.

### D. Cibles produites et action non prescrite

Vérifie que les cibles sont calculées par élimination des décisions exécutées et application de l'action ou conservation de la continuation. Une cible fournie avec une égalité, ou une cible prescrite dont la trace est reconstruite après coup, ne remplit pas la condition forte.

Tente les deux mutations. Tente aussi de remplacer l'action par une sortie canonique constante. Répare ses égalités sur l'échantillon canonique si elles sont réparables, puis conserve le contrat sur les données arbitraires. Un succès seulement sur les données canoniques n'établit pas l'action totale annoncée.

Distingue l'accord `canonicalPayload_accepted` et la convergence des sorties canoniques de la préservation sur toute continuation. Ne déduis pas que toutes les données arbitraires produisent la même valeur.

### E. Préservation et distinction dans l'admission

Vérifie que la préservation du critère pour les continuations arbitraires et la persistance des occurrences distinctes sont effectivement utilisées par la justification du regroupement. Retire chaque garantie séparément ; poursuis au-delà d'un champ ou d'un test nommé.

Inspecte `RoleSemantics.profilePreserves`, `sourcesRemainDistinct`, `profileConstitutionFromChain`, `SemanticImage.certify`, `Specification`, `use`, `viable_iff`, puis leurs instanciations. Vérifie l'acceptation exacte considérée : le critère des profils est point par point sur les continuations locales. Ne l'assimile pas sans preuve à une solution globale d'un arbre adaptatif ou à une affectation commune réalisant toutes les histoires.

L'action doit rester définie sans preuve préalable d'acceptation. La distinction doit justifier « sans identification » ; ne transforme pas artificiellement cette distinction en précondition de toute action brute. Vérifie aussi la viabilité positive de l'alternative absorbée et de chaque profil selon le critère annoncé.

Si la preuve retirée est reconstructible depuis la relation conservée, fournis cette reconstruction et trace sa dépendance. Une copie dispensable et une garantie dispensable ne sont pas la même conclusion. La mutation n'est néanmoins pas rejetée : son statut doit rester visible dans la table forte A–J.

### F. Autorisation et obligation sémantiquement utilisable

Examine le passage de la chaîne causale à `ExecutedOperationalGroupingAuthorization.imageSpecification`, puis à `AuthorizedProducedTargetObligation`, à `transformPayload` et aux consommateurs publics. Détermine ce qui relève de l'appartenance à l'image, de son admission et du portage d'une garantie réellement consommée.

Tente : retrait de l'autorisation ; remplacement de la garantie portée par `True` ; reconstruction de cette garantie depuis une réduction riche restée accessible ; régime `Unit` indépendant ; `carry` constant vers un ancrage. Répare les premières erreurs de champs/projections/noms, puis conserve les obligations sémantiques et d'exactitude publiques.

Ce n'est pas l'impossibilité de définir un singleton abstrait qu'il faut prouver. Il faut éprouver sa capacité à remplacer le régime exécuté exact et autorisé pour ces profils. Ne donne pas un faux rejet en gardant un appel syntaxique à un champ supprimé. Ne donne pas un faux succès en redéfinissant la spécification pour qu'elle n'affirme plus la même chose.

### G. Image exacte et fibres

Vérifie les deux directions de :

```text
carry p = carry q ↔ normalization.target p = normalization.target q
```

et leur raccord aux deux traces de `OperationallyCoDetermined`. Le régime ne doit ni fusionner des cibles produites distinctes, ni séparer des cibles produites égales. Vérifie la complétude et l'absence de doublons de sa frontière, la surjectivité de `carry`, la conservation de la source de chaque trace et de la cible effectivement produite.

La largeur un doit se lire après la convergence et l'exactitude de l'image. Une énumération singleton est admissible si sa complétude sur l'image réelle est démontrée ; elle ne constitue pas à elle seule une preuve de convergence. Le porteur ambiant des continuations ne doit pas avoir été rendu singleton pour obtenir le résultat.

### H. Équivalence exponentielle et généralité

Vérifie le véritable `iff` pour toute famille binaire formalisée, tout problème et tout régime surjectif concerné :

```text
regime.frontier.length = 2 ^ family.stageCount problem
  ↔ Function.Injective regime.carry
```

L'adressage séparé doit être construit à travers les obligations depuis l'injectivité, non ajouté indépendamment. Vérifie le régime identitaire, l'existence du membre binaire indépendant de l'exemple SAT, le caractère non borné prévu par la classe et, séparément, la formule à arités variables comme produit des arités réalisées.

N'élargis pas « exactement `2^n` » à « toute croissance exponentielle ». Inversement, ne déclare pas erronée la conclusion fixée parce qu'elle ne prétend pas cette généralisation. Le lemme fini abstrait est un composant ; il ne prouve pas à lui seul la cible complète.

### I. Mêmes profils, statuts opérationnels différents

Sur le même porteur, vérifie : profils distincts explicites ; continuations canoniques acceptées ; traces exécutées vers une cible commune ; portage commun sans égalité des sources ; régime conservatif distinct de pleine largeur.

Relie les résultats du nouveau théorème commun à l'exécution et à la normalisation qui font autorité. Vérifie que `extensiveMultiplicity_doesNotForceFullOperationalWidth` utilise ce régime exécuté, pas un singleton fabriqué indépendamment.

Sépare la largeur extensive, la frontière en attente, la largeur du régime final et les lectures locales transitoires. Inspecte `widthTrace`, `widthTrace_existing`, la borne deux et les objets dont les nombres sont lus. Vérifie qu'aucune énumération exhaustive des `2^n` profils n'est implicitement présentée comme une opération de largeur constante. Ne convertis pas les bornes de ces lectures en bornes globales de temps ou de mémoire.

### J. Compilation, constructivité et fermeture publique

Depuis le checkout propre au SHA cible, exécute réellement :

```bash
lean --version
lake clean
lake build +RelationalPerimeter
lake build
bash scripts/verify.sh
pwsh -NoProfile -File scripts/verify.ps1
git diff --check
git status --porcelain
git rev-parse HEAD
```

Enregistre stdout, stderr et code de sortie séparément pour chaque commande. Un contrôle impossible dans ton environnement est `NOT RUN`, pas `PASS`. Les résultats annoncés par l'auteur ne remplacent pas tes propres exécutions.

Vérifie que tous les modules de production sont atteignables depuis `import RelationalPerimeter` et que la stratification terminale A5 → A6 → A7 → A8 → A9 est contrôlée dans les scripts Bash et PowerShell. Compare les vérificateurs, tests d'échec, configuration Lake et manifeste aux révisions parentes : une règle affaiblie doit être identifiée. Un ajout d'entrée au manifeste n'est pas en lui-même un assouplissement.

Vérifie exactement un bloc final `AXIOM_AUDIT` dans chaque fichier Lean pertinent. Recherche dans les sources effectives `axiom`, `sorry`, `admit`, `noncomputable`, `Classical`, `propext`, `Quot.sound`, `native_decide`, `unsafe`, `implemented_by` ; distingue code, commentaires, chaînes et fixtures d'échec. Contrôle les dépendances transitives des théorèmes, pas seulement l'absence lexicale des noms.

Inventorie aussi les auxiliaires générés : récursors, éliminateurs, théorèmes d'injectivité, équations et déclarations dérivées. **Ne confonds pas leurs dépendances avec une invocation dans les sources ou une dépendance d'un théorème central.** Pour `propext` et `Quot.sound`, indique chaque origine et si elle est atteignable transitivement depuis les résultats audités. Leur présence dans un auxiliaire généré inutilisé n'établit pas à elle seule que la démonstration source les utilise. Ne transforme pas l'exigence de distinguer les origines en interdiction supplémentaire de tout auxiliaire du compilateur.

Les `sorryAx` éventuellement émis après une erreur d'élaboration dans une copie mutée ne constituent jamais une preuve acceptée. Identifie le premier défaut, corrige la sonde lorsque c'est légitime et recompile ; n'utilise aucun résultat dépendant d'un trou.

## 5. Tests antérieurs à reproduire sans préjuger leur résultat

Le dossier de préparation joint des éléments antérieurs comme **témoignages à revérifier**, jamais comme validation indépendante d'Aristotle :

- `evidence/bridge-verification.json` et ses journaux : commandes annoncées réussies sur `1ca8e89...` ;
- `evidence/new-proof-axioms.log` : sorties annoncées des nouvelles déclarations ;
- `historical-mutations-ded0e8e/A5-store-but-ignore-evidence/` et `A6-public-four-families-Unit/` : patches et résultats d'une campagne sur le parent `ded0e8e...`.

Dans ces deux variantes historiques, les accords sont récupérés depuis les rôles et occurrences riches conservés en amont. Les résultats enregistrent une compilation propre et les deux vérificateurs réussis, sans modification des tests. **Ce ne sont pas des mutations rejetées.** Reproduis-les sur leur parent, puis rebase-les de manière cohérente sur la cible et vérifie aussi les nouveaux clients du raccord. Ne présume pas que 383 lignes de preuves ajoutées rendent ces variantes impossibles.

Les autres premières passes de cette campagne ne constituent pas une table complète validée : plusieurs s'arrêtaient sur des erreurs de syntaxe, de noms ou des preuves non adaptées. Aucun de ces défauts de préparation ne doit être transformé en validation d'une dépendance. Construis tes propres sondes cohérentes pour tous les cas A–J requis.

## 6. Discipline des mutations

Une copie jetable par variante. Enregistre le SHA de départ et le patch complet. Vérifie un témoin non modifié dans le même dispositif. Conserve l'historique des réparations de la sonde et distingue la première erreur superficielle de la première erreur substantielle.

Pour chaque variante finale, lance une compilation propre de la racine, la compilation complète et les deux vérificateurs, puis le contrôle de diff. Si un échec amont empêche un test aval, indique cette causalité ; ne le compte pas comme un second rejet indépendant. Si un processus expire, classe `INCONCLUSIVE`, pas `REJECTED`.

Classification obligatoire des observations :

- `SURVIVES` : les mêmes contrats publics et leurs clients passent ; préciser la garantie conservée ou reconstruite ;
- `SUBSTANTIVE REJECTION` : une obligation constitutive, sémantique ou d'exactitude inchangée ne peut plus être typée/prouvée dans la variante testée ; donner l'erreur et sa raison ;
- `SUPERFICIAL FAILURE` : syntaxe, nom, champ, confidentialité, test non adapté, linter ; réparer et continuer ;
- `INCONCLUSIVE` ou `NOT RUN` : limites d'exécution, environnement ou analyse encore insuffisante.

Un échec d'un corps de preuve particulier ne démontre pas l'impossibilité de toute preuve équivalente. Cherche la réparation cohérente pertinente avant de conclure à la nécessité d'une donnée. Inversement, un succès obtenu en affaiblissant l'énoncé, en supprimant un client substantiel ou en introduisant des hypothèses n'est pas une survie de la cible.

Le protocole n'exige pas d'interdire toute réécriture extensionnellement équivalente par un artifice d'opacité. Lorsque l'exigence forte de rejet dépasse les propriétés effectivement formalisées, explique précisément cet écart au lieu de modifier l'objectif ou de masquer le succès de la mutation.

## 7. Rapport unique attendu

Produis un document autonome `audit/<TARGET>/RAPPORT_ADVERSARIAL_ARISTOTLE.fr.md` et les pièces techniques nécessaires : manifestes, sources des sondes, patches, journaux et résultats structurés. Le rapport doit contenir, dans cet ordre :

1. identité des révisions, environnement, commandes et intégrité avant/après ;
2. lecture des quatre paragraphes sans reformulation réductrice, avec leurs hypothèses et quantificateurs exacts ;
3. carte des neuf niveaux constitutifs : fichier, déclaration, producteur, consommateur, garantie et rôle réel ;
4. analyse détaillée du nouveau raccord et des preuves endogènes antérieures qu'il consomme ;
5. verdict phrase par phrase et champ par champ : `VERIFIED`, `QUALIFIED` ou `FALSE`, avec lignes et preuves ;
6. résultats A–J et table complète des mutations, y compris celles qui survivent ;
7. inventaire des axiomes, séparant sources, dépendances transitives et auxiliaires générés ;
8. divergences entre documentation et Lean, chacune accompagnée de l'énoncé réellement démontré ;
9. périmètre exact : instance exécutée, classe générale, profils, critère local, largeurs et limites ;
10. conclusion directe sur l'objectif scientifique puis verdict global du protocole.

Table minimale pour chaque mutation : identifiant, clause, SHA de base, fichiers modifiés, patch, contrat inchangé, commandes/codes de sortie, premier défaut substantiel, origine du rejet, données encore récupérables, effet précis sur la phrase visée. N'invente aucune preuve de nécessité à partir du seul nom d'une déclaration.

Le verdict global final est exactement l'un de :

```text
EXACT TARGET ESTABLISHED
EXACT TARGET REQUIRES CORRECTIONS
EXACT TARGET NOT ESTABLISHED
```

`EXACT TARGET ESTABLISHED` requiert les quatre paragraphes et toutes les dépendances obligatoires `VERIFIED`, avec les mutations fortes rejetées pour des raisons substantielles. Un paragraphe `FALSE` impose `EXACT TARGET NOT ESTABLISHED`. Un paragraphe ou contrôle `QUALIFIED`, un cas obligatoire non testé ou une mutation obligatoire survivante interdit le verdict positif et permet au mieux `EXACT TARGET REQUIRES CORRECTIONS`.

**N'assimile pas le verdict global de ce protocole fort à la négation de tous les théorèmes présents.** Termine par une réponse lisible : ce qui est démontré, ce qui ne l'est pas, la dépendance exacte restant en cause, et les preuves ou contre-exemples qui justifient ces distinctions. N'exécute aucune réparation du dépôt cible pendant cet audit.
