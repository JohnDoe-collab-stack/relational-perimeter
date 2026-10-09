# Carte des fondations relationnelles

Document généré depuis `knowledge.json` et `sota.json` ; modifier les données, puis régénérer.

Référence : arbre de travail de `codex/positive-circular-foundations`, basé sur le commit `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685`, analyse du 2026-10-09. Les ajouts ne sont pas encore committés.

42 résultats T2, 12 voies réfutées, 9 questions suivies et 2 pistes T6. Certaines questions sont désormais résolues dans un périmètre précis. Ces nombres ne mesurent pas la part totale de recherche résolue.

Les résultats T2 sont propres au projet. Leur compilation Lean et leur relecture IA sont deux contrôles distincts ; une vérification humaine reste en attente. Les interfaces du plan de reconstruction sont des propositions tant qu’une déclaration précise et sa preuve ne les réalisent pas.

Le plan de reconstruction est un fichier local non suivi par Git, consigné par empreinte dans `evidence/source-snapshot.json`. Sa référence historique ne remplace pas une vérification sur la révision courante.

Les liens du graphe sont des dépendances sélectionnées et relues. Ils ne sont pas une extraction exhaustive des termes Lean, ni une preuve de nécessité minimale de chaque hypothèse. `supports` exprime un soutien mathématique ; `uses` signale un raccord explicite sélectionné.

## Résultats et hypothèses

### Unicité résiduelle du noyau

`th.residual` · T2 · refereed

Toute occurrence nouvelle porte le centre résiduel ; deux nouvelles occurrences coïncident. Une partie nouvelle positive fournit une occurrence distinguée unique.

**Hypothèses.** Rôle résiduel contractile, exclusion des étiquettes internes et injectivité du nouvel étiquetage ; positivité pour fournir un habitant.

**Preuve consommée.** label_is_residual utilise l’exclusion et la contraction ; occurrences_unique utilise ensuite newLabelInjective.

**Déclarations.**

- `SegmentedResidualRole.ResidualDeterminationCore.occurrences_unique` — [SegmentedResidualRole.lean:136](../SegmentedResidualRole.lean).
- `SegmentedResidualRole.positiveCore_hasUniqueResidualOccurrence` — [SegmentedResidualRole.lean:167](../SegmentedResidualRole.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Reconstruction interne sous conditions supplémentaires

`th.internal-reconstruction` · T2 · refereed

Un noyau résiduel positif reconstruit ExactInternalCompletion si embedOld est injectif ; la positivité permet de retrouver des étiquettes anciennes internes.

**Hypothèses.** ResidualUniquenessKernel, PositiveNewPart, Function.Injective kernel.embedOld.

**Preuve consommée.** oldLabelsInternal_of_positive puis ExactReconstructionConditions.toExactInternalCompletion.

**Déclarations.**

- `SegmentedResidualRole.ResidualUniquenessKernel.toExactInternalCompletion_of_positive` — [SegmentedResidualRole.lean:595](../SegmentedResidualRole.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Classification et sortie du régime abstrait

`th.abstract-exit` · T2 · refereed

Un régime dont chaque candidat est canonique ou produit une tentative rejetée classe exactement la frontière ; la continuation stricte n’est pas admise.

**Hypothèses.** BoundaryGenerator avec extension irréflexive ; canonicalRegime, classifyOrTotalize, rejectTotalization.

**Preuve consommée.** Classification par analyse des deux branches ; sortie par continuation_ne_boundary.

**Portée.** Résultat conditionnel sur une règle de régime explicite ; ce n’est pas une conséquence de la seule circularité.

**Déclarations.**

- `AbstractSegmentedTurning.ObstructedRegime.exactClassification` — [AbstractSegmentedTurning.lean:352](../AbstractSegmentedTurning.lean).
- `AbstractSegmentedTurning.ObstructedRegime.continuation_outside_regime` — [AbstractSegmentedTurning.lean:370](../AbstractSegmentedTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Accord des applications directes et unicité de l’inverse

`th.transport-backward` · T2 · refereed

Deux ExactTypeTransport dont les fonctions directes coïncident point par point ont des fonctions inverses qui coïncident point par point.

**Hypothèses.** Deux applications dans chaque sens et leurs lois de retour ; accord ponctuel des fonctions directes.

**Preuve consommée.** Lois de retour des deux transports et forwardAgreement.

**Portée.** Le transport exact entre porteurs ne contient pas d’accord relationnel supplémentaire.

**Déclarations.**

- `ExactTypeTransport.backward_eq_of_forward_eq` — [ExactTypeTransport.lean:101](../ExactTypeTransport.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Correspondance exacte positions–occurrences

`th.perimeter-exact` · T2 · refereed

Les positions non fermantes et les occurrences du déploiement canonique se correspondent avec deux lois de retour.

**Hypothèses.** Présentation P et déploiement canonique de sa chaîne successive.

**Preuve consommée.** Inductions et décodage du déploiement ; cette correspondance ne réalise pas finalJunction comme occurrence intérieure.

**Déclarations.**

- `StrongPerimetralTurning.occurrenceToRequirement_toOccurrence` — [StrongPerimetralTurning.lean:3197](../StrongPerimetralTurning.lean).
- `StrongPerimetralTurning.requirementToOccurrence_toRequirement` — [StrongPerimetralTurning.lean:3205](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Injectivité, ordre et adjacence dans une histoire réelle

`th.rooted-structure` · T2 · refereed

Toute ExactNonClosingRealization dans une RootedGeneratedHistory est injective, conserve la précédence et la succession immédiate.

**Hypothèses.** Histoire réellement générée, enracinée et composable ; accords exacts source/cible et curseurs.

**Preuve consommée.** Trichotomie des occurrences, futurs stricts irréflexifs, accords des curseurs et des états.

**Portée.** Ne vaut pas pour le carrier affaibli SemanticTrace ; adjacence signifie ici succession immédiate.

**Déclarations.**

- `StrongPerimetralTurning.ExactNonClosingRealization.realize_injective` — [StrongPerimetralTurning.lean:4040](../StrongPerimetralTurning.lean).
- `StrongPerimetralTurning.ExactNonClosingRealization.preservesPrecedence` — [StrongPerimetralTurning.lean:4084](../StrongPerimetralTurning.lean).
- `StrongPerimetralTurning.ExactNonClosingRealization.preservesNext` — [StrongPerimetralTurning.lean:4115](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Factorisation constructive par le périmètre

`th.factorization` · T2 · refereed

Une ExactNonClosingRealization dans une histoire enracinée reconstruit une continuation et la recomposition de cette histoire depuis le périmètre canonique.

**Hypothèses.** ExactNonClosingRealization P history sur RootedGeneratedHistory.

**Preuve consommée.** factorDeployRemainingFromExactOccurrences, injectivité reconstruite et accords des pas localisés.

**Portée.** La continuation reconstruite peut être root, donc vide ; ce résultat ne garantit pas un suffixe strictement positif.

**Déclarations.**

- `StrongPerimetralTurning.ExactNonClosingRealization.toPerimeterExtension` — [StrongPerimetralTurning.lean:4654](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Continuation positivement engendrée et stricte

`th.positive-continuation` · T2 · refereed

oneStepAfterPerimeter construit un pas après le périmètre et une extension stricte, distincte du déploiement canonique.

**Hypothèses.** CircularPresentation P et le générateur libre courant.

**Preuve consommée.** Génération effective, histoire singleton positive et irréflexivité du préfixe strict.

**Déclarations.**

- `StrongPerimetralTurning.oneStepAfterPerimeterStrict` — [StrongPerimetralTurning.lean:2705](../StrongPerimetralTurning.lean).
- `StrongPerimetralTurning.oneStepAfterPerimeter_ne` — [StrongPerimetralTurning.lean:2715](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Absence de retour dans une histoire générée positive

`th.no-return` · T2 · refereed

Une histoire GeneratedHistory positive possède une source distincte de sa cible.

**Hypothèses.** History.Positive (@GeneratedStep P) source target, sur les PositiveConstitution P de la présentation.

**Preuve consommée.** Avancée positive des curseurs et irréflexivité.

**Portée.** Résultat sur cette génération libre ; ne dit pas que des systèmes de transition arbitraires sont sans cycles.

**Déclarations.**

- `StrongPerimetralTurning.positiveGeneratedHistory_source_ne_target` — [StrongPerimetralTurning.lean:2556](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Toute continuation positive fidèlement classée a un résidu unique

`th.labelled-residual` · T2 · refereed

Dans une FaithfullyLabelledPerimeterExtension positive, toute nouvelle occurrence porte FinalRequirement et les occurrences de la continuation sont uniques.

**Hypothèses.** Extension périmétrale, étiquetage fidèle préservant les anciennes positions et continuation positive.

**Preuve consommée.** Passage vers SegmentedResidualRole et contractibilité de FinalRequirement.

**Portée.** Le noyau canonique oneStepResidualDeterminationCore définit séparément un label final constant et utilise ExactlyOne pour son injectivité ; ne pas confondre les deux chemins de preuve.

**Déclarations.**

- `StrongPerimetralTurning.FaithfullyLabelledPerimeterExtension.newOccurrence_label_is_final` — [StrongPerimetralTurning.lean:5211](../StrongPerimetralTurning.lean).
- `StrongPerimetralTurning.FaithfullyLabelledPerimeterExtension.continuation_occurrences_unique` — [StrongPerimetralTurning.lean:5221](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Maximalité relative au régime circulaire

`th.circular-classification` · T2 · refereed

CircularRefinement P history équivaut constructivement à history = perimeterDeployment P ; le premier pas supplémentaire n’est pas admis.

**Hypothèses.** Règles de CircularRefinement, notamment realizesFinal, et obstruction de CircularPresentation.

**Preuve consommée.** Classification du tournant couplé historique ; la branche positive impose une tentative de totalisation rejetée.

**Portée.** La génération continue ; cette maximalité est relative au régime choisi.

**Déclarations.**

- `StrongPerimetralTurning.exactCircularRefinementClassification` — [StrongPerimetralTurning.lean:6853](../StrongPerimetralTurning.lean).
- `StrongPerimetralTurning.oneStepAfterPerimeter_notCircularRefinement` — [StrongPerimetralTurning.lean:6864](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Admission et satisfaction : adéquation démontrée

`th.specification` · T2 · refereed

CircularRefinement fournit CircularSpecificationSatisfaction ; réciproquement la satisfaction fournit le raffinement, avec des témoins et interfaces distincts.

**Hypothèses.** Spécification avec exactitude locale et clause trajectorielle ; obstruction au TotalLoop.

**Preuve consommée.** Factorisation locale, classification du périmètre et rejet de la tentative produite par une extension stricte.

**Déclarations.**

- `StrongPerimetralTurning.circularRefinement_soundSpecification` — [StrongPerimetralTurning.lean:6906](../StrongPerimetralTurning.lean).
- `StrongPerimetralTurning.circularSpecification_complete` — [StrongPerimetralTurning.lean:6086](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Certificat du tournant périmétral affirmatif

`th.turning` · T2 · refereed

strongPerimetralTurning rassemble génération positive, réalisation exacte, absorption des parties admissibles, refus des totalisations et continuation au-delà du périmètre.

**Hypothèses.** CircularPresentation avec ses données et son obstruction initiale.

**Preuve consommée.** Assemblage de résultats déjà construits ; voir les champs et leurs producteurs, sans déduire une dépendance causale de leur seule présence.

**Déclarations.**

- `StrongPerimetralTurning.strongPerimetralTurning` — [StrongPerimetralTurning.lean:7001](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Lecture numérique dérivée des histoires

`th.numeric-readout` · T2 · refereed

Une histoire perimétralement admissible a une longueur inférieure ou égale à celle du déploiement canonique.

**Hypothèses.** PerimetrallyAdmissible P history, soit une partie libre soit un raffinement du même périmètre.

**Preuve consommée.** admissible_is_prefix_of_perimeter et monotonie de History.length sur les préfixes.

**Portée.** History.length compte les pas ; ne constitue pas l’identité ni les relations des occurrences.

**Déclarations.**

- `StrongPerimetralTurning.admissible_length_le_perimeter` — [StrongPerimetralTurning.lean:7138](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Interprétation exacte des occurrences concrètes

`th.concrete-interpretation` · T2 · refereed

Toute ConcreteContinuationAlgebra fournit une ExactHistoryInterpretation de chaque histoire libre, avec deux retours des occurrences.

**Hypothèses.** ConcreteContinuationAlgebra avec son interface de pas concrets et ses accords primitifs ; les applications et retours des occurrences sont reconstruits par induction.

**Preuve consommée.** realizeHistory, applications entre occurrences, lois concreteBackwardForward et concreteForwardBackward.

**Portée.** Ne fournit pas l’injectivité de toutes les lectures d’états ou de valeurs ; la fidélité des cibles exige une hypothèse propre.

**Déclarations.**

- `StrongPerimetralTurning.exactlyInterpretHistory` — [StrongPerimetralTurning.lean:7607](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Séparateur existant : exactitude locale sans ordre

`th.separator-order` · T2 · refereed

La réalisation sémantique permutée de l’exemple à quatre nœuds est localement exacte et injective, mais ne conserve pas la précédence.

**Hypothèses.** SemanticTrace affaiblie et examplePresentation ; contre-exemple dans cette présentation.

**Preuve consommée.** Permutation explicite, inversion des deux premières adresses et asymétrie de Nat.lt.

**Déclarations.**

- `StrongPerimetralTurning.Example.permutedExample_not_order_preserved` — [StrongPerimetralTurning.lean:8161](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Séparateur existant : ordre sans pont composable

`th.separator-bridge` · T2 · refereed

La trace intercalée de l’exemple conserve la précédence mais n’a pas de pont constitutif effectif entre les première et deuxième positions adjacentes.

**Hypothèses.** SemanticTrace de l’exemple, accord local et occurrences supplémentaires intercalées.

**Preuve consommée.** Positions ordonnées 0, 2, 4 ; occurrence intercalaire et bridgeParticipation_between_empty_of_next.

**Déclarations.**

- `StrongPerimetralTurning.Example.interleavedExample_order_preserved` — [StrongPerimetralTurning.lean:8284](../StrongPerimetralTurning.lean).
- `StrongPerimetralTurning.Example.interleavedExample_no_effective_bridge_p1_p2` — [StrongPerimetralTurning.lean:8356](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Nouveau contre-modèle : retirer la fidélité détruit l’unicité

`th.separator-injectivity` · T2 · refereed

Deux nouvelles occurrences Bool ont le même label dans un résidu Unit contractile, sans aucun label interne Empty, et restent distinctes.

**Hypothèses.** Core affaibli : injectivité du nouvel étiquetage supprimée ; anciennes occurrences absentes.

**Preuve consommée.** Étiquette constante sur Bool ; false ≠ true.

**Déclarations.**

- `FoundationalSeparators.weakened_core_does_not_force_uniqueness` — [labyrinth/probes/FoundationalSeparators.lean.in:33](../labyrinth/probes/FoundationalSeparators.lean.in).
- `FoundationalSeparators.residual_label_not_injective` — [labyrinth/probes/FoundationalSeparators.lean.in:27](../labyrinth/probes/FoundationalSeparators.lean.in).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Nouveau contre-modèle : transport exact sans conservation de l’ordre

`th.separator-transport` · T2 · refereed

L’involution Bool.not est un ExactTypeTransport Bool Bool qui inverse une relation Before false true et ne la préserve pas.

**Hypothèses.** Deux lois de retour ; aucune obligation de conservation de Before dans ExactTypeTransport.

**Preuve consommée.** Bool.not et élimination de Before true false.

**Déclarations.**

- `FoundationalSeparators.swap_does_not_preserve_order` — [labyrinth/probes/FoundationalSeparators.lean.in:80](../labyrinth/probes/FoundationalSeparators.lean.in).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Diagnostic : le rôle final nu est uniformément ponctuel

`th.final-role-carrier` · T2 · refereed

Pour toute présentation P, FinalRequirement P possède un transport exact explicite vers Unit.

**Hypothèses.** Uniquement le type inductif FinalRequirement P à un constructeur.

**Preuve consommée.** Élimination du rôle et de Unit ; aucune jonction ni occurrence n’est transportée.

**Portée.** Diagnostic du porteur nu, sans verdict sur une interface enrichie par une frontière, un témoin ou un morphisme.

**Déclarations.**

- `FoundationalSeparators.finalRoleUnitTransport` — [labyrinth/probes/FoundationalSeparators.lean.in:86](../labyrinth/probes/FoundationalSeparators.lean.in).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Nouveau contre-modèle : positivité sans reconstruction intérieure

`th.separator-old-completion` · T2 · refereed

Un ResidualUniquenessKernel peut avoir une partie nouvelle positive et un résidu unique sans admettre aucune ExactInternalCompletion : les anciennes occurrences peuvent être fusionnées par embedOld.

**Hypothèses.** Ancien porteur Bool, rôle interne Unit et partie nouvelle Unit ; plongement ancien constant. Deux constructions distinctes, avec porteurs étendus Bool et Option Unit.

**Preuve consommée.** Le retour occurrenceRoundTrip de la complétion demandée forcerait false = true ou true = false. Le noyau segmenté conserve pourtant un étiquetage étendu fidèle et la positivité nouvelle.

**Portée.** Réfute la suppression de l’injectivité ancienne dans la reconstruction ; ne met pas en cause l’unicité résiduelle.

**Déclarations.**

- `FoundationReferee.collapsedOld_no_exact_completion` — [research/agents/referee-foundations/IndependentProbes.lean.in:35](../research/agents/referee-foundations/IndependentProbes.lean.in).
- `FoundationalSeparators.positive_kernel_does_not_force_internal_completion` — [labyrinth/probes/FoundationalSeparators.lean.in:65](../labyrinth/probes/FoundationalSeparators.lean.in).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Présentation positive et obstruction séparées

`th.positive-split` · T2 · refereed

Les données circulaires positives sont définies sans rejet de contraction. Une même chaîne reçoit des lectures de pôles identifiés ou séparés ; seule la seconde reçoit l’obstruction de l’exemple.

**Hypothèses.** Chaîne positive et jonction reçues en entrée ; séparation dérivée seulement avec CircularClosureObstruction.

**Preuve consommée.** Le modèle Unit identifie les pôles ; l’obstruction Bool rejetant false = true enrichit le même parent positif.

**Portée.** Aucune algèbre générale d’engendrement, ni boucle d’exécution historique périodique.

**Déclarations.**

- `StrongPerimetralTurning.PositiveCircularPresentation` — [RelationalPerimeter/Constitution/PositivePresentation.lean:18](../RelationalPerimeter/Constitution/PositivePresentation.lean).
- `StrongPerimetralTurning.CircularClosureObstruction.endpointsSeparated` — [RelationalPerimeter/Constitution/PositivePresentation.lean:62](../RelationalPerimeter/Constitution/PositivePresentation.lean).
- `RelationalPerimeter.Constitution.Examples.identifiedBoundary_no_obstruction` — [RelationalPerimeter/Constitution/Examples.lean:46](../RelationalPerimeter/Constitution/Examples.lean).
- `RelationalPerimeter.Constitution.Examples.same_positive_data` — [RelationalPerimeter/Constitution/Examples.lean:68](../RelationalPerimeter/Constitution/Examples.lean).

**Relecture.** Énoncé et portée relus par un referee IA indépendant ; sondes propres sur cinq porteurs et deux échanges distincts. Build complet et contrôle constructif par le coordinateur. Vérification humaine en attente.

### Reconstruction exacte de la présentation historique

`th.circular-bridge` · T2 · refereed

Extraire la présentation positive, la frontière de pôles et l’obstruction puis les réassembler reconstruit exactement CircularPresentation ; les trois couches ont aussi leurs lois de retour.

**Hypothèses.** Présentation historique, ou présentation positive équipée d’une frontière et d’une obstruction.

**Preuve consommée.** Les quatre retours sont établis par réduction et analyse de structure ; tous les champs et témoins sont conservés.

**Portée.** Le pont conserve l’interface historique consommée par les preuves et la partie computationnelle.

**Déclarations.**

- `StrongPerimetralTurning.CircularPresentation.positive_roundTrip` — [RelationalPerimeter/Constitution/CircularPresentationBridge.lean:48](../RelationalPerimeter/Constitution/CircularPresentationBridge.lean).
- `StrongPerimetralTurning.CircularPresentation.boundary_roundTrip` — [RelationalPerimeter/Constitution/CircularPresentationBridge.lean:55](../RelationalPerimeter/Constitution/CircularPresentationBridge.lean).
- `StrongPerimetralTurning.CircularPresentation.obstruction_roundTrip` — [RelationalPerimeter/Constitution/CircularPresentationBridge.lean:63](../RelationalPerimeter/Constitution/CircularPresentationBridge.lean).
- `StrongPerimetralTurning.CircularPresentation.historical_roundTrip` — [RelationalPerimeter/Constitution/CircularPresentationBridge.lean:72](../RelationalPerimeter/Constitution/CircularPresentationBridge.lean).

**Relecture.** Énoncé et portée relus par un referee IA indépendant ; sondes propres sur cinq porteurs et deux échanges distincts. Build complet et contrôle constructif par le coordinateur. Vérification humaine en attente.

### Extraction autoritative de la frontière de clôture

`th.boundary-extraction` · T2 · refereed

closingBoundary extrait la source implicite terminale, la cible explicite initiale, la jonction fermante distinguée et la différence/provenance initiales.

**Hypothèses.** PositiveCircularPresentation déjà pointée par sa jonction fermante.

**Preuve consommée.** Les champs sont lus directement depuis la même présentation ; les vues de jonction et provenance sont définitoires.

**Portée.** Signature sélectionnée ; aucune nouvelle occurrence ni transport de toutes les fibres.

**Déclarations.**

- `RelationalPerimeter.Constitution.closingBoundary` — [RelationalPerimeter/Constitution/BoundaryTransport.lean:31](../RelationalPerimeter/Constitution/BoundaryTransport.lean).
- `PositiveFoundationReferee.extractedBoundaryReadsExactData` — [research/agents/referee-positive-foundations/IndependentProbes.lean.in:145](../research/agents/referee-positive-foundations/IndependentProbes.lean.in).

**Relecture.** Énoncé et portée relus par un referee IA indépendant ; sondes propres sur cinq porteurs et deux échanges distincts. Build complet et contrôle constructif par le coordinateur. Vérification humaine en attente.

### Calcul constructif des transports équipés de frontière

`th.boundary-calculus` · T2 · refereed

Les transports exacts des cinq porteurs conservant trois indices et deux témoins sont fermés par identité, inversion et composition. Unités, associativité et inverses valent point par point ; l’accord inverse se déduit de l’accord direct.

**Hypothèses.** Cinq ExactTypeTransport ; sourceExact, targetExact, differenceExact, junctionExact et provenanceExact.

**Preuve consommée.** Inversion par lois de retour et congrArg ; composition des cinq accords ; égalité inverse par backward_eq_of_forward_eq.

**Portée.** Fibres de compatibilité et provenance sélectionnées seulement ; aucune égalité globale de structures de fonctions.

**Déclarations.**

- `RelationalPerimeter.Constitution.BoundaryTransport.reverse` — [RelationalPerimeter/Constitution/BoundaryTransport.lean:79](../RelationalPerimeter/Constitution/BoundaryTransport.lean).
- `RelationalPerimeter.Constitution.BoundaryTransport.compose` — [RelationalPerimeter/Constitution/BoundaryTransport.lean:102](../RelationalPerimeter/Constitution/BoundaryTransport.lean).
- `RelationalPerimeter.Constitution.BoundaryTransport.identity_left` — [RelationalPerimeter/Constitution/BoundaryTransport.lean:133](../RelationalPerimeter/Constitution/BoundaryTransport.lean).
- `RelationalPerimeter.Constitution.BoundaryTransport.identity_right` — [RelationalPerimeter/Constitution/BoundaryTransport.lean:138](../RelationalPerimeter/Constitution/BoundaryTransport.lean).
- `RelationalPerimeter.Constitution.BoundaryTransport.compose_associative` — [RelationalPerimeter/Constitution/BoundaryTransport.lean:143](../RelationalPerimeter/Constitution/BoundaryTransport.lean).
- `RelationalPerimeter.Constitution.BoundaryTransport.reverse_left` — [RelationalPerimeter/Constitution/BoundaryTransport.lean:150](../RelationalPerimeter/Constitution/BoundaryTransport.lean).
- `RelationalPerimeter.Constitution.BoundaryTransport.reverse_right` — [RelationalPerimeter/Constitution/BoundaryTransport.lean:157](../RelationalPerimeter/Constitution/BoundaryTransport.lean).
- `RelationalPerimeter.Constitution.BoundaryTransport.backward_of_forward` — [RelationalPerimeter/Constitution/BoundaryTransport.lean:185](../RelationalPerimeter/Constitution/BoundaryTransport.lean).

**Relecture.** Énoncé et portée relus par un referee IA indépendant ; sondes propres sur cinq porteurs et deux échanges distincts. Build complet et contrôle constructif par le coordinateur. Vérification humaine en attente.

### Rôle final équipé et ses retours exacts

`th.equipped-role` · T2 · refereed

Le rôle équipé d’une frontière est habité et unique. Un transport riche conserve ses vues de source, cible et provenance et induit un transport exact du rôle, compatible à l’identité et à la composition.

**Hypothèses.** Frontière déjà munie d’une jonction ; rôle avec witnessExact ; BoundaryTransport conservant le témoin et les indices.

**Preuve consommée.** Extensionalité par égalité des témoins ; conservation lue des cinq accords ; retours par lois du transport de la fibre fermante.

**Portée.** La fibre est contractile. Son porteur seul ne détermine pas les morphismes riches ; grammaire complète des rôles circulaires hors portée.

**Déclarations.**

- `RelationalPerimeter.Constitution.EquippedFinalRole.canonical` — [RelationalPerimeter/Constitution/BoundaryTransport.lean:232](../RelationalPerimeter/Constitution/BoundaryTransport.lean).
- `RelationalPerimeter.Constitution.EquippedFinalRole.unique` — [RelationalPerimeter/Constitution/BoundaryTransport.lean:228](../RelationalPerimeter/Constitution/BoundaryTransport.lean).
- `RelationalPerimeter.Constitution.EquippedFinalRole.source_preserved` — [RelationalPerimeter/Constitution/BoundaryTransport.lean:246](../RelationalPerimeter/Constitution/BoundaryTransport.lean).
- `RelationalPerimeter.Constitution.EquippedFinalRole.target_preserved` — [RelationalPerimeter/Constitution/BoundaryTransport.lean:250](../RelationalPerimeter/Constitution/BoundaryTransport.lean).
- `RelationalPerimeter.Constitution.EquippedFinalRole.provenance_preserved` — [RelationalPerimeter/Constitution/BoundaryTransport.lean:254](../RelationalPerimeter/Constitution/BoundaryTransport.lean).
- `RelationalPerimeter.Constitution.EquippedFinalRole.transport_identity` — [RelationalPerimeter/Constitution/BoundaryTransport.lean:258](../RelationalPerimeter/Constitution/BoundaryTransport.lean).
- `RelationalPerimeter.Constitution.EquippedFinalRole.transport_compose` — [RelationalPerimeter/Constitution/BoundaryTransport.lean:263](../RelationalPerimeter/Constitution/BoundaryTransport.lean).
- `RelationalPerimeter.Constitution.EquippedFinalRole.exactTransport` — [RelationalPerimeter/Constitution/BoundaryTransport.lean:280](../RelationalPerimeter/Constitution/BoundaryTransport.lean).

**Relecture.** Énoncé et portée relus par un referee IA indépendant ; sondes propres sur cinq porteurs et deux échanges distincts. Build complet et contrôle constructif par le coordinateur. Vérification humaine en attente.

### Une bijection de fibre peut perdre la jonction choisie

`th.separator-closing-witness` · T2 · refereed

Un transport exact de tous les porteurs conserve les trois indices mais échange les témoins Bool de clôture ; ce transport spécifié ne peut s’enrichir en BoundaryTransport.

**Hypothèses.** Même frontière pointée ; Bool.not seulement sur la fibre de clôture, identité ailleurs.

**Preuve consommée.** false est envoyé sur true ; junctionExact imposerait true = false.

**Portée.** Ne réfute pas tous les transports riches entre ces frontières : l’identité existe.

**Déclarations.**

- `RelationalPerimeter.Constitution.Examples.closingSwap_preserves_indices` — [RelationalPerimeter/Constitution/Examples.lean:89](../RelationalPerimeter/Constitution/Examples.lean).
- `RelationalPerimeter.Constitution.Examples.closingSwap_cannot_lift` — [RelationalPerimeter/Constitution/Examples.lean:100](../RelationalPerimeter/Constitution/Examples.lean).

**Relecture.** Énoncé et portée relus par un referee IA indépendant ; sondes propres sur cinq porteurs et deux échanges distincts. Build complet et contrôle constructif par le coordinateur. Vérification humaine en attente.

### L’accord de jonction ne conserve pas la provenance

`th.separator-provenance-witness` · T2 · refereed

Un transport exact conserve les trois indices et la jonction mais échange uniquement les témoins Bool de provenance ; il ne peut s’enrichir avec ces mêmes applications.

**Hypothèses.** Modèle indépendant Bool ; identité des quatre autres porteurs.

**Preuve consommée.** provenanceExact contredirait le calcul de Bool.not sur le témoin choisi.

**Portée.** Loi de provenance distincte de la loi de jonction.

**Déclarations.**

- `PositiveFoundationReferee.swapProvenanceOnly` — [research/agents/referee-positive-foundations/IndependentProbes.lean.in:115](../research/agents/referee-positive-foundations/IndependentProbes.lean.in).
- `PositiveFoundationReferee.provenanceSwapCannotEnrich` — [research/agents/referee-positive-foundations/IndependentProbes.lean.in:130](../research/agents/referee-positive-foundations/IndependentProbes.lean.in).

**Relecture.** Modèle original du referee-positive-foundations, relu indépendamment de son auteur par le coordinateur : les trois indices et la jonction sont conservés, provenanceExact impose true = false. Sonde recompilée sans axiomes ; vérification humaine en attente.

### La présentation positive autorise un retour du nœud brut

`th.separator-positive-recurrence` · T2 · refereed

Une présentation positive non vide peut avoir son nœud terminal égal au nœud initial. Cette égalité ne produit pas un retour de curseur ni une occurrence historique cyclique.

**Hypothèses.** Un pas sur le même LocalNode et témoin fermant reçu.

**Preuve consommée.** Le retour du nœud est rfl ; les curseurs historiques restent indexés par leur prolongement.

**Portée.** Modèle de données positives, sans théorème de génération périodique.

**Déclarations.**

- `RelationalPerimeter.Constitution.Examples.raw_node_return` — [RelationalPerimeter/Constitution/Examples.lean:72](../RelationalPerimeter/Constitution/Examples.lean).
- `PositiveFoundationReferee.repeatedRawNode` — [research/agents/referee-positive-foundations/IndependentProbes.lean.in:47](../research/agents/referee-positive-foundations/IndependentProbes.lean.in).

**Relecture.** Énoncé et portée relus par un referee IA indépendant ; sondes propres sur cinq porteurs et deux échanges distincts. Build complet et contrôle constructif par le coordinateur. Vérification humaine en attente.

### Frontière sans jonction et reconstruction exacte

`th.closing-shape-bridge` · T2 · refereed

ClosingBoundaryShape omet seulement la jonction. Un pointage indexé fournit ce témoin ; oubli et reconstruction ont des retours exacts pour la forme, le pointage et la ConstitutiveBoundary actuelle.

**Hypothèses.** Sortes, familles, source/cible, différence et provenance initiales sélectionnées ; jonction fournie pour reconstruire la frontière équipée.

**Preuve consommée.** Les champs sont copiés directement ; les trois retours sont obtenus par réduction et analyse du pointage.

**Portée.** La provenance et les indices restent choisis ; aucune minimalité universelle de signature.

**Déclarations.**

- `RelationalPerimeter.Constitution.ConstitutiveBoundary.toClosingBoundaryShape` — [RelationalPerimeter/Constitution/ClosingBoundary.lean:62](../RelationalPerimeter/Constitution/ClosingBoundary.lean).
- `RelationalPerimeter.Constitution.PointedClosingBoundary.toConstitutiveBoundary` — [RelationalPerimeter/Constitution/ClosingBoundary.lean:83](../RelationalPerimeter/Constitution/ClosingBoundary.lean).
- `RelationalPerimeter.Constitution.PointedClosingBoundary.shape_roundTrip` — [RelationalPerimeter/Constitution/ClosingBoundary.lean:96](../RelationalPerimeter/Constitution/ClosingBoundary.lean).
- `RelationalPerimeter.Constitution.PointedClosingBoundary.pointing_roundTrip` — [RelationalPerimeter/Constitution/ClosingBoundary.lean:99](../RelationalPerimeter/Constitution/ClosingBoundary.lean).
- `RelationalPerimeter.Constitution.ConstitutiveBoundary.boundary_roundTrip` — [RelationalPerimeter/Constitution/ClosingBoundary.lean:123](../RelationalPerimeter/Constitution/ClosingBoundary.lean).

**Relecture.** Referee IA indépendant : lot 1 établi dans sa portée, propres sondes à fibres dépendantes et données sélectionnées distinctes ; 20 audits sans axiomes. Coordinateur : modèles recoupés, build complet et contrôle global réussis. Vérification humaine en attente.

### Témoin concret, pointage exact et habitation propositionnelle

`th.closing-pointing-exact` · T2 · refereed

La fibre ClosingWitness B et PointedClosingBoundary B sont reliées par un transport exact. Leur habitation est équivalente dans Prop ; le constructeur de pointage reçoit un témoin concret dans Type.

**Hypothèses.** Une forme de frontière B ; témoin de sa fibre fermante pour point.

**Preuve consommée.** Constructeur et projection de jonction ont deux retours ; Nonempty est éliminé seulement vers une proposition.

**Portée.** L’équivalence d’habitation ne constitue pas une fonction de choix depuis Nonempty vers Type.

**Déclarations.**

- `RelationalPerimeter.Constitution.ClosingBoundaryShape.pointingTransport` — [RelationalPerimeter/Constitution/ClosingBoundary.lean:41](../RelationalPerimeter/Constitution/ClosingBoundary.lean).
- `RelationalPerimeter.Constitution.ClosingBoundaryShape.nonempty_pointed_iff` — [RelationalPerimeter/Constitution/ClosingBoundary.lean:48](../RelationalPerimeter/Constitution/ClosingBoundary.lean).
- `RelationalPerimeter.Constitution.ClosingBoundaryShape.noPointingOfEmpty` — [RelationalPerimeter/Constitution/ClosingBoundary.lean:52](../RelationalPerimeter/Constitution/ClosingBoundary.lean).

**Relecture.** Referee IA indépendant : lot 1 établi dans sa portée, propres sondes à fibres dépendantes et données sélectionnées distinctes ; 20 audits sans axiomes. Coordinateur : modèles recoupés, build complet et contrôle global réussis. Vérification humaine en attente.

### Une fibre fermante vide interdit le choix et son rôle

`th.closing-empty` · T2 · refereed

Une forme peut avoir une fibre fermante vide. Aucun pointage ni choix accompagné d’un rôle n’existe alors. Cette forme vide ne peut être l’oubli d’une ConstitutiveBoundary déjà équipée.

**Hypothèses.** ClosingWitness B → False ; modèle direct à fibre Empty, indices et provenance initiale disponibles.

**Preuve consommée.** Tout pointage fournirait une jonction ; une frontière équipée fournit déjà un habitant de sa fibre oubliée, contradictoire avec Empty.

**Portée.** Le modèle vide est construit avant le pointage, sans être présenté comme extraction d’une présentation déjà fermée.

**Déclarations.**

- `RelationalPerimeter.Constitution.ClosingBoundaryShape.noFinalRoleOfEmpty` — [RelationalPerimeter/Constitution/ClosingBoundary.lean:136](../RelationalPerimeter/Constitution/ClosingBoundary.lean).
- `RelationalPerimeter.Constitution.ClosingBoundaryExamples.empty_no_pointing` — [RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean:31](../RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean).
- `RelationalPerimeter.Constitution.ClosingBoundaryExamples.empty_no_final_role` — [RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean:34](../RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean).
- `RelationalPerimeter.Constitution.ClosingBoundaryExamples.empty_not_from_constitutive` — [RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean:38](../RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean).

**Relecture.** Referee IA indépendant : lot 1 établi dans sa portée, propres sondes à fibres dépendantes et données sélectionnées distinctes ; 20 audits sans axiomes. Coordinateur : modèles recoupés, build complet et contrôle global réussis. Vérification humaine en attente.

### Rôle habité et unique pour chaque jonction choisie

`th.closing-role-choice` · T2 · refereed

Pour chaque pointage fixé, le rôle final adapté est habité et unique, et son témoin est exactement la jonction de ce pointage. L’existence d’un choix avec rôle équivaut à l’habitation de la fibre fermante.

**Hypothèses.** PointedClosingBoundary B fixé ; rôle accordé au témoin de la frontière reconstruite.

**Preuve consommée.** Canonical et unique du rôle équipé actuel ; witnessExact donne la vue de jonction ; les équivalences d’existence restent propositionnelles.

**Portée.** Aucune unicité de tous les pointages, classification complète des rôles, ni occurrence nouvelle engendrée.

**Déclarations.**

- `RelationalPerimeter.Constitution.PointedClosingBoundary.finalRole` — [RelationalPerimeter/Constitution/ClosingBoundary.lean:109](../RelationalPerimeter/Constitution/ClosingBoundary.lean).
- `RelationalPerimeter.Constitution.PointedClosingBoundary.finalRole_unique` — [RelationalPerimeter/Constitution/ClosingBoundary.lean:112](../RelationalPerimeter/Constitution/ClosingBoundary.lean).
- `RelationalPerimeter.Constitution.PointedClosingBoundary.finalRole_junction` — [RelationalPerimeter/Constitution/ClosingBoundary.lean:116](../RelationalPerimeter/Constitution/ClosingBoundary.lean).
- `RelationalPerimeter.Constitution.ClosingBoundaryShape.nonempty_finalRole_iff` — [RelationalPerimeter/Constitution/ClosingBoundary.lean:130](../RelationalPerimeter/Constitution/ClosingBoundary.lean).

**Relecture.** Referee IA indépendant : lot 1 établi dans sa portée, propres sondes à fibres dépendantes et données sélectionnées distinctes ; 20 audits sans axiomes. Coordinateur : modèles recoupés, build complet et contrôle global réussis. Vérification humaine en attente.

### Deux choix distincts malgré l’unicité du rôle par choix

`th.closing-choice-multiplicity` · T2 · refereed

Une fibre Unit possède un témoin unique. Une même forme à fibre Bool reçoit deux pointages distincts, chacun avec rôle unique ; sa fibre de témoins et sa fibre de pointages ne sont pas uniques.

**Hypothèses.** Modèles directs à compatibilité constante Unit ou Bool ; pointages false et true du même boolShape.

**Preuve consommée.** Projection de toute égalité des pointages sur leur jonction ; contradiction par constructeurs distincts de Bool ; unicité du rôle quantifie un pointage fixé.

**Portée.** Contre-modèle à une unicité globale déduite de l’unicité par choix. Le diagnostic Sigma original du referee n’est pas ajouté comme résultat distinct.

**Déclarations.**

- `RelationalPerimeter.Constitution.ClosingBoundaryExamples.unit_fibre_unique` — [RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean:50](../RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean).
- `RelationalPerimeter.Constitution.ClosingBoundaryExamples.bool_pointings_distinct` — [RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean:70](../RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean).
- `RelationalPerimeter.Constitution.ClosingBoundaryExamples.bool_per_choice_role_unique` — [RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean:84](../RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean).
- `RelationalPerimeter.Constitution.ClosingBoundaryExamples.bool_closing_fibre_not_unique` — [RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean:95](../RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean).

**Relecture.** Referee IA indépendant : lot 1 établi dans sa portée, propres sondes à fibres dépendantes et données sélectionnées distinctes ; 20 audits sans axiomes. Coordinateur : modèles recoupés, build complet et contrôle global réussis. Vérification humaine en attente.

### Déploiement depuis une formation positive reçue

`th.positive-formation-deployment` · T2 · refereed

Une formation reçoit états, nœuds et pas admissibles avec leur compatibilité. Toute histoire finie composable déploie une épine conservant le départ, le terme et les paquets de nœuds/compatibilité lus à chaque pas.

**Hypothèses.** PositiveFormation, nœuds déjà témoins, Step indexé et compatibility(step) ; histoire de pas concrets.

**Preuve consommée.** Récursion nil/cons ; égalité du nœud terminal par induction ; deploy_link_exact conserve le paquet SuccessiveLink entier.

**Portée.** Les pas et primitives sont reçus. Le déploiement peut oublier des données supplémentaires de Step ; aucune injectivité générale sur les histoires.

**Déclarations.**

- `RelationalPerimeter.Constitution.PositiveFormation` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:70](../RelationalPerimeter/Constitution/PositiveGeneration.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.deploy_start` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:128](../RelationalPerimeter/Constitution/PositiveGeneration.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.deploy_final` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:131](../RelationalPerimeter/Constitution/PositiveGeneration.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.deploy_link_exact` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:207](../RelationalPerimeter/Constitution/PositiveGeneration.lean).

**Relecture.** Referee IA indépendant : lot 2 établi dans la signature de chemins/déploiement ; 38 sondes sans axiomes, données différentes et réindexation vérifiée. Coordinateur : modèles recoupés, build et script global réussis. Vérification humaine en attente.

### Composition des histoires et réindexation du déploiement

`th.positive-history-composition` · T2 · refereed

La composition des histoires possède deux unités et est associative. Le déploiement de la composition est la composition des épines, avec transport du suffixe le long du raccord terminal exact.

**Hypothèses.** Histoires dont les états intermédiaires coïncident ; deploy_final fournit finalNode = node cible.

**Preuve consommée.** Induction sur la première histoire ; congrArg sur cons/advance ; appendAlong explicite la réindexation du suffixe.

**Portée.** L’accord d’indices fait partie du théorème. Pas de propriété universelle des chemins ni de transport des opérations entre formations.

**Déclarations.**

- `RelationalPerimeter.Constitution.PositiveHistory.nil_append` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:105](../RelationalPerimeter/Constitution/PositiveGeneration.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.append_nil` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:108](../RelationalPerimeter/Constitution/PositiveGeneration.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.append_associative` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:115](../RelationalPerimeter/Constitution/PositiveGeneration.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.deploy_append` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:137](../RelationalPerimeter/Constitution/PositiveGeneration.lean).

**Relecture.** Referee IA indépendant : lot 2 établi dans la signature de chemins/déploiement ; 38 sondes sans axiomes, données différentes et réindexation vérifiée. Coordinateur : modèles recoupés, build et script global réussis. Vérification humaine en attente.

### Occurrences et positions du déploiement avec deux retours

`th.positive-occurrence-positions` · T2 · refereed

Les occurrences des pas d’une histoire correspondent exactement aux positions non fermantes de son déploiement. L’histoire vide n’a aucune occurrence ; here et later sont distincts dans une même histoire.

**Hypothèses.** PositiveHistory donnée ; occurrences indexées par nil/cons et NonClosingPosition du déploiement.

**Preuve consommée.** Conversion here/later par récursion ; les deux retours par induction ; distinction des constructeurs.

**Portée.** Occurrences de cette nouvelle histoire positive ; aucune identification automatique au générateur historique strict.

**Déclarations.**

- `RelationalPerimeter.Constitution.PositiveHistory.nil_noOccurrence` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:152](../RelationalPerimeter/Constitution/PositiveGeneration.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.here_ne_later` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:155](../RelationalPerimeter/Constitution/PositiveGeneration.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.positionTransport` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:194](../RelationalPerimeter/Constitution/PositiveGeneration.lean).

**Relecture.** Referee IA indépendant : lot 2 établi dans la signature de chemins/déploiement ; 38 sondes sans axiomes, données différentes et réindexation vérifiée. Coordinateur : modèles recoupés, build et script global réussis. Vérification humaine en attente.

### Clôture explicite du déploiement positif

`th.positive-explicit-closing` · T2 · refereed

Une histoire extrait une forme de frontière sans jonction. Une occurrence et une jonction concrète permettent ensuite de construire une présentation positive conservant le nœud initial, le déploiement, la jonction et la frontière équipée.

**Hypothèses.** Occurrence history dans Type et ClosingWitness history.boundaryShape, fournis séparément.

**Preuve consommée.** boundary_source_exact dérive la lecture terminale ; toCircular lit les champs de la même histoire et les deux données fournies.

**Portée.** La positivité seule ne construit aucune jonction ; aucune extraction depuis une existence propositionnelle.

**Déclarations.**

- `RelationalPerimeter.Constitution.PositiveHistory.boundary_source_exact` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:226](../RelationalPerimeter/Constitution/PositiveGeneration.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.toCircular_initial` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:244](../RelationalPerimeter/Constitution/PositiveGeneration.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.toCircular_deployment` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:248](../RelationalPerimeter/Constitution/PositiveGeneration.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.toCircular_junction` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:252](../RelationalPerimeter/Constitution/PositiveGeneration.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.toCircular_boundary` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:256](../RelationalPerimeter/Constitution/PositiveGeneration.lean).

**Relecture.** Referee IA indépendant : lot 2 établi dans la signature de chemins/déploiement ; 38 sondes sans axiomes, données différentes et réindexation vérifiée. Coordinateur : modèles recoupés, build et script global réussis. Vérification humaine en attente.

### Enrichissement historique après la génération positive

`th.positive-generated-historical-bridge` · T2 · refereed

Ajouter les lectures de pôles et leur obstruction à une présentation positivement déployée reconstruit CircularPresentation avec accords exacts des trois couches et du déploiement.

**Hypothèses.** Histoire positive, jonction, EndpointBoundary et CircularClosureObstruction sur la même présentation construite.

**Preuve consommée.** Le module pont applique ofPositive et les trois retours existants ; son épine est celle du déploiement.

**Portée.** Le cœur de génération ne consomme aucun rejet de contraction. Les lois du GeneratedStep historique ne sont pas attribuées à tout Step abstrait.

**Déclarations.**

- `RelationalPerimeter.Constitution.PositiveHistory.historical_positive` — [RelationalPerimeter/Constitution/PositiveGenerationBridge.lean:24](../RelationalPerimeter/Constitution/PositiveGenerationBridge.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.historical_endpoints` — [RelationalPerimeter/Constitution/PositiveGenerationBridge.lean:32](../RelationalPerimeter/Constitution/PositiveGenerationBridge.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.historical_obstruction` — [RelationalPerimeter/Constitution/PositiveGenerationBridge.lean:39](../RelationalPerimeter/Constitution/PositiveGenerationBridge.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.historical_deployment` — [RelationalPerimeter/Constitution/PositiveGenerationBridge.lean:46](../RelationalPerimeter/Constitution/PositiveGenerationBridge.lean).

**Relecture.** Referee IA indépendant : lot 2 établi dans la signature de chemins/déploiement ; 38 sondes sans axiomes, données différentes et réindexation vérifiée. Coordinateur : modèles recoupés, build et script global réussis. Vérification humaine en attente.

### Continuation choisie distincte de l’admissibilité des pas

`th.positive-successor-choice` · T2 · refereed

Une continuation globale choisie est une donnée supplémentaire permettant une itération finie positive dès un pas. Une formation peut permettre deux successeurs distincts, ou ne pas posséder de continuation globale.

**Hypothèses.** ChosenPositiveContinuation fournit successor et un pas depuis chaque état ; modèles branchingFormation et directedFormation.

**Preuve consommée.** walk construit nil/cons ; le modèle branchant fixe deux successeurs distincts, le modèle dirigé n’a aucun pas depuis true.

**Portée.** Aucun déterminisme ni disponibilité d’un pas dans toute PositiveFormation ; le compteur pilote seulement cette itération.

**Déclarations.**

- `RelationalPerimeter.Constitution.ChosenPositiveContinuation.walk` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:270](../RelationalPerimeter/Constitution/PositiveGeneration.lean).
- `RelationalPerimeter.Constitution.ChosenPositiveContinuation.walk_successor_positive` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:277](../RelationalPerimeter/Constitution/PositiveGeneration.lean).
- `RelationalPerimeter.Constitution.PositiveGenerationExamples.branching_targets_distinct` — [RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:129](../RelationalPerimeter/Constitution/PositiveGenerationExamples.lean).
- `RelationalPerimeter.Constitution.PositiveGenerationExamples.chosen_successors_distinct` — [RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:141](../RelationalPerimeter/Constitution/PositiveGenerationExamples.lean).
- `RelationalPerimeter.Constitution.PositiveGenerationExamples.directed_no_global_continuation` — [RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:52](../RelationalPerimeter/Constitution/PositiveGenerationExamples.lean).

**Relecture.** Referee IA indépendant : lot 2 établi dans la signature de chemins/déploiement ; 38 sondes sans axiomes, données différentes et réindexation vérifiée. Coordinateur : modèles recoupés, build et script global réussis. Vérification humaine en attente.

### Génération positive sans clôture disponible

`th.separator-generated-unclosed` · T2 · refereed

Un pas admissible false→true déploie une chaîne positive, tandis que sa fibre fermante true→false est Empty. Aucun pointage ne ferme cette chaîne générée.

**Hypothèses.** Compatibilité dirigée, DirectedStep.forward, histoire d’un pas et indices du déploiement.

**Preuve consommée.** directedPositive donne here ; la fibre fermante calcule Empty ; noPointingOfEmpty interdit le pointage.

**Portée.** Contre-modèle à une clôture automatiquement déduite de positivité, sans réfuter les présentations recevant une jonction distincte.

**Déclarations.**

- `RelationalPerimeter.Constitution.PositiveGenerationExamples.directedPositive` — [RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:43](../RelationalPerimeter/Constitution/PositiveGenerationExamples.lean).
- `RelationalPerimeter.Constitution.PositiveGenerationExamples.directed_closing_empty` — [RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:45](../RelationalPerimeter/Constitution/PositiveGenerationExamples.lean).
- `RelationalPerimeter.Constitution.PositiveGenerationExamples.directed_no_pointing` — [RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:48](../RelationalPerimeter/Constitution/PositiveGenerationExamples.lean).

**Relecture.** Referee IA indépendant : lot 2 établi dans la signature de chemins/déploiement ; 38 sondes sans axiomes, données différentes et réindexation vérifiée. Coordinateur : modèles recoupés, build et script global réussis. Vérification humaine en attente.

### Retour de nœud brut sans fusion des positions

`th.separator-repeated-positive-occurrences` · T2 · refereed

Deux pas peuvent lire le même nœud brut dans une histoire positive finie, tout en ayant des occurrences et positions distinctes et des témoins de compatibilité distincts.

**Hypothèses.** repeatedHistory sur Unit, pas true puis false, occurrences here et later here.

**Preuve consommée.** Égalité des nœuds par réduction ; distinctness des constructeurs et retour du transport de positions ; true ≠ false pour les témoins.

**Portée.** Un retour d’état est permis par PositiveHistory. Le non-retour des curseurs historiques ne s’étend pas à cette interface générique.

**Déclarations.**

- `RelationalPerimeter.Constitution.PositiveGenerationExamples.raw_nodes_repeat` — [RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:159](../RelationalPerimeter/Constitution/PositiveGenerationExamples.lean).
- `RelationalPerimeter.Constitution.PositiveGenerationExamples.repeated_occurrences_distinct` — [RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:163](../RelationalPerimeter/Constitution/PositiveGenerationExamples.lean).
- `RelationalPerimeter.Constitution.PositiveGenerationExamples.repeated_positions_distinct` — [RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:166](../RelationalPerimeter/Constitution/PositiveGenerationExamples.lean).
- `RelationalPerimeter.Constitution.PositiveGenerationExamples.repeated_step_witnesses_distinct` — [RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:172](../RelationalPerimeter/Constitution/PositiveGenerationExamples.lean).

**Relecture.** Referee IA indépendant : lot 2 établi dans la signature de chemins/déploiement ; 38 sondes sans axiomes, données différentes et réindexation vérifiée. Coordinateur : modèles recoupés, build et script global réussis. Vérification humaine en attente.

## Voies réfutées et leçons

### L’exactitude locale imposerait l’ordre sur toute trace

Réfuté sur SemanticTrace par l’exemple permuté.

**Leçon.** L’ordre reconstruit requiert la composition et l’enracinement du carrier fort.

### L’ordre suffirait à la participation composable

Réfuté sur SemanticTrace par l’exemple intercalé.

**Leçon.** Conserver la précédence ne fournit pas un pont constitutif effectif entre positions adjacentes.

### Contractibilité et exclusion suffiraient à l’unicité

Réfuté par deux occurrences Bool portant le même label final.

**Leçon.** Garder l’injectivité du nouvel étiquetage ; ce contre-modèle teste sa suppression, sans prouver une minimalité de toutes les hypothèses.

### Le transport exact entre types conserverait toute relation

Réfuté par le transport Bool.not sur Before.

**Leçon.** Ajouter des accords relationnels explicites aux deux lois de retour.

### La positivité du noyau suffirait à reconstruire l’intérieur exact

Réfuté par deux anciens Bool fusionnés dans un noyau pourtant positif et fidèlement étiqueté sur son porteur étendu.

**Leçon.** Pour reconstruire la réalisation intérieure, conserver l’injectivité de embedOld ; la positivité permet seulement de retrouver les étiquettes anciennes internes.

### La bijection exacte conserverait le témoin choisi

Réfuté par Bool.not sur la fibre de compatibilité fermante, avec trois indices inchangés.

**Leçon.** Exiger junctionExact en plus des lois de retour.

### Conserver la jonction suffirait à conserver la provenance

Réfuté par un échange de provenance indépendant, sans changement des indices ni de la jonction.

**Leçon.** Exiger provenanceExact séparément.

### La positivité circulaire interdirait tout retour du nœud brut

Réfuté par une chaîne positive d’un pas sur le même nœud.

**Leçon.** Distinguer nœuds bruts, curseurs et occurrences engendrées.

### L’unicité du rôle par choix imposerait une jonction unique

Réfuté par une même forme Bool avec deux pointages distincts et un rôle unique sur chaque pointage.

**Leçon.** Fixer le choix dans la quantification du théorème de rôle ; ne pas identifier la fibre de rôles sur un choix avec la famille de tous les choix.

### Une chaîne positive fournirait sa propre jonction

Réfuté par une histoire dirigée positive dont la fibre fermante est Empty.

**Leçon.** Fournir une jonction distincte pour la clôture ; séparer existence de pas et existence de boucle fermante.

### La formation admissible déterminerait un successeur unique

Réfuté par deux pas depuis le même état vers deux cibles différentes, et deux continuations choisies différentes.

**Leçon.** La sélection d’une continuation est une donnée supplémentaire ; les théorèmes canoniques ne sont pas universels.

### Deux lectures du même nœud seraient la même occurrence

Réfuté par deux pas sur le même nœud avec here et later here distincts.

**Leçon.** Conserver l’histoire et la position du pas ; la valeur brute ne suffit pas à identifier l’occurrence.

## Portes de recherche

### Circularité positive autonome

`q.positive-circle` · answered

La séparation de la présentation positive et de l’obstruction, ainsi que le retour exact à la présentation historique, sont réalisés. La génération positive générale reste une question distincte.

**Test proposé.** Modèles Unit/Bool sur le même parent positif ; quatre lois exactes du pont historique.

### Rôle final équipé de sa frontière

`q.equipped-final-role` · partial

Le rôle de clôture équipé, la forme de frontière sans jonction choisie et son enrichissement exact sont réalisés. Les modèles vide/Unit/Bool distinguent existence, choix et unicité par choix. La grammaire circulaire complète et la minimalité générale restent ouvertes.

**Test proposé.** Construire les branches intérieure/finale équipées et leurs raccords aux occurrences ; tester la conservation de cette classification.

### Transport de la constitution relationnelle

`q.rich-transport` · partial

Identité, inversion et composition sont réalisées pour la frontière sélectionnée, avec accords source/cible/différence et témoins de jonction/provenance. Le transport des familles complètes reste ouvert.

**Test proposé.** Étendre les applications à toutes les fibres Compatible et Provenance puis aux opérations constitutives.

### Réalisation choisie et rigidité

`q.rigidity` · open

Comment séparer une réalisation exacte distinguée de la propriété selon laquelle toute réalisation admissible impose la même classification ?

**Test proposé.** Modèle avec deux réalisations possibles, puis interface optionnelle de rigidité et théorème de classification.

### Plusieurs témoins ou successeurs

`q.multiple-generation` · open

Le mécanisme du tournant peut-il être formulé sur une génération générale à plusieurs successeurs tout en conservant la continuation choisie ?

**Test proposé.** Construire deux successeurs non identifiés et coupler le certificat à l’un d’eux ; ne pas réutiliser implicitement la détermination par curseur.

### Quantité structurelle générale

`q.quantity` · open

Quelle signature et quel critère d’équivalence constituent une quantité structurelle au-delà de la seule correspondance de porteurs ?

**Test proposé.** Deux systèmes de même cardinalité et de relations différentes ; vérifier qu’un morphisme de quantité conserve les accords choisis.

### Converse d’une reconstruction de trace

`q.converse-traces` · open

Sous quelles hypothèses supplémentaires une trace localement exacte, ordonnée et contiguë se reconstruit-elle en histoire enracinée composable ?

**Test proposé.** Définir précisément la contiguïté, tester les séparateurs puis fournir raccords source/cible et racine ; établir la propriété dans les deux sens.

### Fidélité des cibles sous interprétation

`q.concrete-faithfulness` · open

Quelles hypothèses sur ConcreteContinuationAlgebra préservent la distinction de la cible fermante et de la continuation libre ?

**Test proposé.** Construire ou récupérer une algèbre concrète qui fusionne les lectures, puis ajouter l’accord suffisant de séparation.

### Algèbre de génération positive générale

`q.positive-generation` · answered

Une PositiveFormation reçue engendre des histoires finies composables et leur épine, avec nœuds, positions et lectures de compatibilité exacts. Une jonction distincte ferme la chaîne positive ; elle ne se déduit pas de la positivité seule.

**Test proposé.** Quatre modèles : chaîne dirigée sans clôture, chaîne fermée, deux successeurs admissibles, nœud brut répété avec positions distinctes.

## Pistes T6 — spéculation explicite

### Comparer les frontières par des morphismes équipés

La piste a une réalisation T2 pour la signature de clôture sélectionnée. Son extension à toute la constitution relationnelle reste spéculative.

**Test.** Étendre la signature et chercher des séparateurs des accords manquants.

### Propriété universelle des histoires

Une propriété universelle de chemins libres pourrait clarifier la reconstruction et le transport de la génération ; elle n’est pas établie ici.

**Test.** Définir les morphismes compatibles aux pas et prouver une extension unique point par point dans le cadre constructif.

## État des questions suivi

| Question | Statut |
|---|---|
| Unicité résiduelle du noyau | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Reconstruction interne sous conditions supplémentaires | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Classification et sortie du régime abstrait | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Accord des applications directes et unicité de l’inverse | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Correspondance exacte positions–occurrences | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Injectivité, ordre et adjacence dans une histoire réelle | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Factorisation constructive par le périmètre | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Continuation positivement engendrée et stricte | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Absence de retour dans une histoire générée positive | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Toute continuation positive fidèlement classée a un résidu unique | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Maximalité relative au régime circulaire | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Admission et satisfaction : adéquation démontrée | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Certificat du tournant périmétral affirmatif | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Lecture numérique dérivée des histoires | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Interprétation exacte des occurrences concrètes | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Séparateur existant : exactitude locale sans ordre | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Séparateur existant : ordre sans pont composable | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Nouveau contre-modèle : retirer la fidélité détruit l’unicité | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Nouveau contre-modèle : transport exact sans conservation de l’ordre | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Diagnostic : le rôle final nu est uniformément ponctuel | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Circularité positive autonome | Données positives, pont et génération relative réalisés T2 |
| Rôle final équipé de sa frontière | Lot 1 réalisé T2 et relu ; classification complète et minimalité générale ouvertes |
| Transport de la constitution relationnelle | Réponse partielle T2 ; extension générale ouverte |
| Réalisation choisie et rigidité | Question ouverte ; interface non acquise |
| Plusieurs témoins ou successeurs | Question ouverte ; interface non acquise |
| Quantité structurelle générale | Question ouverte ; interface non acquise |
| Converse d’une reconstruction de trace | Question ouverte ; interface non acquise |
| Fidélité des cibles sous interprétation | Question ouverte ; interface non acquise |
| Nouveau contre-modèle : positivité sans reconstruction intérieure | T2 · deux constructions Lean ; referee IA et contrôle du coordinateur ; vérification humaine en attente |
| Présentation positive et obstruction séparées | T2 · Lean compilé ; referee IA indépendant (referee-positive-foundations) ; vérification humaine en attente |
| Reconstruction exacte de la présentation historique | T2 · Lean compilé ; referee IA indépendant (referee-positive-foundations) ; vérification humaine en attente |
| Extraction autoritative de la frontière de clôture | T2 · Lean compilé ; referee IA indépendant (referee-positive-foundations) ; vérification humaine en attente |
| Calcul constructif des transports équipés de frontière | T2 · Lean compilé ; referee IA indépendant (referee-positive-foundations) ; vérification humaine en attente |
| Rôle final équipé et ses retours exacts | T2 · Lean compilé ; referee IA indépendant (referee-positive-foundations) ; vérification humaine en attente |
| Une bijection de fibre peut perdre la jonction choisie | T2 · Lean compilé ; referee IA indépendant (referee-positive-foundations) ; vérification humaine en attente |
| L’accord de jonction ne conserve pas la provenance | T2 · modèle du referee, relecture indépendante par le coordinateur ; Lean compilé ; vérification humaine en attente |
| La présentation positive autorise un retour du nœud brut | T2 · Lean compilé ; referee IA indépendant (referee-positive-foundations) ; vérification humaine en attente |
| Algèbre de génération positive générale | Lot 2 réalisé T2 et relu · formation relative, clôture conditionnelle |
| Frontière sans jonction et reconstruction exacte | T2 · Lean compilé ; referee IA indépendant (referee-closing-boundary) ; vérification humaine en attente |
| Témoin concret, pointage exact et habitation propositionnelle | T2 · Lean compilé ; referee IA indépendant (referee-closing-boundary) ; vérification humaine en attente |
| Une fibre fermante vide interdit le choix et son rôle | T2 · Lean compilé ; referee IA indépendant (referee-closing-boundary) ; vérification humaine en attente |
| Rôle habité et unique pour chaque jonction choisie | T2 · Lean compilé ; referee IA indépendant (referee-closing-boundary) ; vérification humaine en attente |
| Deux choix distincts malgré l’unicité du rôle par choix | T2 · Lean compilé ; referee IA indépendant (referee-closing-boundary) ; vérification humaine en attente |
| Déploiement depuis une formation positive reçue | T2 · Lean compilé ; referee IA indépendant (referee-positive-generation) ; humain en attente |
| Composition des histoires et réindexation du déploiement | T2 · Lean compilé ; referee IA indépendant (referee-positive-generation) ; humain en attente |
| Occurrences et positions du déploiement avec deux retours | T2 · Lean compilé ; referee IA indépendant (referee-positive-generation) ; humain en attente |
| Clôture explicite du déploiement positif | T2 · Lean compilé ; referee IA indépendant (referee-positive-generation) ; humain en attente |
| Enrichissement historique après la génération positive | T2 · Lean compilé ; referee IA indépendant (referee-positive-generation) ; humain en attente |
| Continuation choisie distincte de l’admissibilité des pas | T2 · Lean compilé ; referee IA indépendant (referee-positive-generation) ; humain en attente |
| Génération positive sans clôture disponible | T2 · Lean compilé ; referee IA indépendant (referee-positive-generation) ; humain en attente |
| Retour de nœud brut sans fusion des positions | T2 · Lean compilé ; referee IA indépendant (referee-positive-generation) ; humain en attente |

## Première prochaine exploration

Les lots 1 et 2 sont achevés : frontière avant choix et génération relative de chemins finis, avec clôture par témoin distinct. Prochaine tranche : transport des familles complètes (`q.rich-transport`, lot 3A), puis des opérations de formation (lot 3B). La grammaire circulaire complète des rôles (`q.equipped-final-role`, lot 4) reste ouverte.

Aucun atlas taille × invariant n’est défini pour ce chantier architectural. `frontier.json` reste absent plutôt que de produire une fraction artificielle de questions résolues.
