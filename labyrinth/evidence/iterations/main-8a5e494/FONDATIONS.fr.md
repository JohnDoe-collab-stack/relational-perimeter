# Carte des fondations relationnelles

Document généré depuis `knowledge.json` et `sota.json` ; modifier les données, puis régénérer.

Référence : `main`, commit `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685`, analyse du 2026-10-09.

21 résultats T2, 5 voies réfutées, 8 questions ouvertes et 2 pistes spéculatives. Ces nombres décrivent les éléments suivis, pas la part totale de recherche résolue.

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

- `StrongPerimetralTurning.occurrenceToRequirement_toOccurrence` — [StrongPerimetralTurning.lean:3400](../StrongPerimetralTurning.lean).
- `StrongPerimetralTurning.requirementToOccurrence_toRequirement` — [StrongPerimetralTurning.lean:3408](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Injectivité, ordre et adjacence dans une histoire réelle

`th.rooted-structure` · T2 · refereed

Toute ExactNonClosingRealization dans une RootedGeneratedHistory est injective, conserve la précédence et la succession immédiate.

**Hypothèses.** Histoire réellement générée, enracinée et composable ; accords exacts source/cible et curseurs.

**Preuve consommée.** Trichotomie des occurrences, futurs stricts irréflexifs, accords des curseurs et des états.

**Portée.** Ne vaut pas pour le carrier affaibli SemanticTrace ; adjacence signifie ici succession immédiate.

**Déclarations.**

- `StrongPerimetralTurning.ExactNonClosingRealization.realize_injective` — [StrongPerimetralTurning.lean:4243](../StrongPerimetralTurning.lean).
- `StrongPerimetralTurning.ExactNonClosingRealization.preservesPrecedence` — [StrongPerimetralTurning.lean:4287](../StrongPerimetralTurning.lean).
- `StrongPerimetralTurning.ExactNonClosingRealization.preservesNext` — [StrongPerimetralTurning.lean:4318](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Factorisation constructive par le périmètre

`th.factorization` · T2 · refereed

Une ExactNonClosingRealization dans une histoire enracinée reconstruit une continuation et la recomposition de cette histoire depuis le périmètre canonique.

**Hypothèses.** ExactNonClosingRealization P history sur RootedGeneratedHistory.

**Preuve consommée.** factorDeployRemainingFromExactOccurrences, injectivité reconstruite et accords des pas localisés.

**Portée.** La continuation reconstruite peut être root, donc vide ; ce résultat ne garantit pas un suffixe strictement positif.

**Déclarations.**

- `StrongPerimetralTurning.ExactNonClosingRealization.toPerimeterExtension` — [StrongPerimetralTurning.lean:4857](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Continuation positivement engendrée et stricte

`th.positive-continuation` · T2 · refereed

oneStepAfterPerimeter construit un pas après le périmètre et une extension stricte, distincte du déploiement canonique.

**Hypothèses.** CircularPresentation P et le générateur libre courant.

**Preuve consommée.** Génération effective, histoire singleton positive et irréflexivité du préfixe strict.

**Déclarations.**

- `StrongPerimetralTurning.oneStepAfterPerimeterStrict` — [StrongPerimetralTurning.lean:2908](../StrongPerimetralTurning.lean).
- `StrongPerimetralTurning.oneStepAfterPerimeter_ne` — [StrongPerimetralTurning.lean:2918](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Absence de retour dans une histoire générée positive

`th.no-return` · T2 · refereed

Une histoire GeneratedHistory positive possède une source distincte de sa cible.

**Hypothèses.** History.Positive (@GeneratedStep P) source target, sur les PositiveConstitution P de la présentation.

**Preuve consommée.** Avancée positive des curseurs et irréflexivité.

**Portée.** Résultat sur cette génération libre ; ne dit pas que des systèmes de transition arbitraires sont sans cycles.

**Déclarations.**

- `StrongPerimetralTurning.positiveGeneratedHistory_source_ne_target` — [StrongPerimetralTurning.lean:2759](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Toute continuation positive fidèlement classée a un résidu unique

`th.labelled-residual` · T2 · refereed

Dans une FaithfullyLabelledPerimeterExtension positive, toute nouvelle occurrence porte FinalRequirement et les occurrences de la continuation sont uniques.

**Hypothèses.** Extension périmétrale, étiquetage fidèle préservant les anciennes positions et continuation positive.

**Preuve consommée.** Passage vers SegmentedResidualRole et contractibilité de FinalRequirement.

**Portée.** Le noyau canonique oneStepResidualDeterminationCore définit séparément un label final constant et utilise ExactlyOne pour son injectivité ; ne pas confondre les deux chemins de preuve.

**Déclarations.**

- `StrongPerimetralTurning.FaithfullyLabelledPerimeterExtension.newOccurrence_label_is_final` — [StrongPerimetralTurning.lean:5414](../StrongPerimetralTurning.lean).
- `StrongPerimetralTurning.FaithfullyLabelledPerimeterExtension.continuation_occurrences_unique` — [StrongPerimetralTurning.lean:5424](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Maximalité relative au régime circulaire

`th.circular-classification` · T2 · refereed

CircularRefinement P history équivaut constructivement à history = perimeterDeployment P ; le premier pas supplémentaire n’est pas admis.

**Hypothèses.** Règles de CircularRefinement, notamment realizesFinal, et obstruction de CircularPresentation.

**Preuve consommée.** Classification du tournant couplé historique ; la branche positive impose une tentative de totalisation rejetée.

**Portée.** La génération continue ; cette maximalité est relative au régime choisi.

**Déclarations.**

- `StrongPerimetralTurning.exactCircularRefinementClassification` — [StrongPerimetralTurning.lean:7056](../StrongPerimetralTurning.lean).
- `StrongPerimetralTurning.oneStepAfterPerimeter_notCircularRefinement` — [StrongPerimetralTurning.lean:7067](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Admission et satisfaction : adéquation démontrée

`th.specification` · T2 · refereed

CircularRefinement fournit CircularSpecificationSatisfaction ; réciproquement la satisfaction fournit le raffinement, avec des témoins et interfaces distincts.

**Hypothèses.** Spécification avec exactitude locale et clause trajectorielle ; obstruction au TotalLoop.

**Preuve consommée.** Factorisation locale, classification du périmètre et rejet de la tentative produite par une extension stricte.

**Déclarations.**

- `StrongPerimetralTurning.circularRefinement_soundSpecification` — [StrongPerimetralTurning.lean:7109](../StrongPerimetralTurning.lean).
- `StrongPerimetralTurning.circularSpecification_complete` — [StrongPerimetralTurning.lean:6289](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Certificat du tournant périmétral affirmatif

`th.turning` · T2 · refereed

strongPerimetralTurning rassemble génération positive, réalisation exacte, absorption des parties admissibles, refus des totalisations et continuation au-delà du périmètre.

**Hypothèses.** CircularPresentation avec ses données et son obstruction initiale.

**Preuve consommée.** Assemblage de résultats déjà construits ; voir les champs et leurs producteurs, sans déduire une dépendance causale de leur seule présence.

**Déclarations.**

- `StrongPerimetralTurning.strongPerimetralTurning` — [StrongPerimetralTurning.lean:7204](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Lecture numérique dérivée des histoires

`th.numeric-readout` · T2 · refereed

Une histoire perimétralement admissible a une longueur inférieure ou égale à celle du déploiement canonique.

**Hypothèses.** PerimetrallyAdmissible P history, soit une partie libre soit un raffinement du même périmètre.

**Preuve consommée.** admissible_is_prefix_of_perimeter et monotonie de History.length sur les préfixes.

**Portée.** History.length compte les pas ; ne constitue pas l’identité ni les relations des occurrences.

**Déclarations.**

- `StrongPerimetralTurning.admissible_length_le_perimeter` — [StrongPerimetralTurning.lean:7341](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Interprétation exacte des occurrences concrètes

`th.concrete-interpretation` · T2 · refereed

Toute ConcreteContinuationAlgebra fournit une ExactHistoryInterpretation de chaque histoire libre, avec deux retours des occurrences.

**Hypothèses.** ConcreteContinuationAlgebra avec son interface de pas concrets et ses accords primitifs ; les applications et retours des occurrences sont reconstruits par induction.

**Preuve consommée.** realizeHistory, applications entre occurrences, lois concreteBackwardForward et concreteForwardBackward.

**Portée.** Ne fournit pas l’injectivité de toutes les lectures d’états ou de valeurs ; la fidélité des cibles exige une hypothèse propre.

**Déclarations.**

- `StrongPerimetralTurning.exactlyInterpretHistory` — [StrongPerimetralTurning.lean:7810](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Séparateur existant : exactitude locale sans ordre

`th.separator-order` · T2 · refereed

La réalisation sémantique permutée de l’exemple à quatre nœuds est localement exacte et injective, mais ne conserve pas la précédence.

**Hypothèses.** SemanticTrace affaiblie et examplePresentation ; contre-exemple dans cette présentation.

**Preuve consommée.** Permutation explicite, inversion des deux premières adresses et asymétrie de Nat.lt.

**Déclarations.**

- `StrongPerimetralTurning.Example.permutedExample_not_order_preserved` — [StrongPerimetralTurning.lean:8364](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Séparateur existant : ordre sans pont composable

`th.separator-bridge` · T2 · refereed

La trace intercalée de l’exemple conserve la précédence mais n’a pas de pont constitutif effectif entre les première et deuxième positions adjacentes.

**Hypothèses.** SemanticTrace de l’exemple, accord local et occurrences supplémentaires intercalées.

**Preuve consommée.** Positions ordonnées 0, 2, 4 ; occurrence intercalaire et bridgeParticipation_between_empty_of_next.

**Déclarations.**

- `StrongPerimetralTurning.Example.interleavedExample_order_preserved` — [StrongPerimetralTurning.lean:8487](../StrongPerimetralTurning.lean).
- `StrongPerimetralTurning.Example.interleavedExample_no_effective_bridge_p1_p2` — [StrongPerimetralTurning.lean:8559](../StrongPerimetralTurning.lean).

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

## Portes de recherche

### Circularité positive autonome

`q.positive-circle` · open

Peut-on séparer une présentation circulaire positive de l’obstruction initiale, puis retrouver l’instance existante par ajout de cette couche ?

**Test proposé.** Construire deux présentations avec même chaîne et même jonction, dont une admet un bouclage et l’autre porte une obstruction ; vérifier l’adaptation aux types actuels.

### Rôle final équipé de sa frontière

`q.equipped-final-role` · open

Quelle structure minimale relie le rôle final, sa frontière et la jonction distinguée, avec des morphismes qui préservent cette origine ?

**Test proposé.** Définir une interface équipée et tester un transport entre deux frontières différentes : la bijection des porteurs nus ne doit pas suffire.

### Transport de la constitution relationnelle

`q.rich-transport` · open

Quels accords source/cible, compatibilité et provenance doivent accompagner un transport exact, et quelles lois de composition restent constructives ?

**Test proposé.** Écrire les accords ponctuels, composer deux morphismes et vérifier les témoins conservés sans extensionalité fonctionnelle.

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

## Pistes T6 — spéculation explicite

### Comparer les frontières par des morphismes équipés

Une interface de frontière avec témoin distingué pourrait fournir une comparaison constitutive plus précise que l’index du rôle ponctuel seul.

**Test.** Prototype de q.equipped-final-role ; tenter une permutation qui conserve le porteur et casse le témoin.

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
| Circularité positive autonome | Question ouverte ; interface non acquise |
| Rôle final équipé de sa frontière | Question ouverte ; interface non acquise |
| Transport de la constitution relationnelle | Question ouverte ; interface non acquise |
| Réalisation choisie et rigidité | Question ouverte ; interface non acquise |
| Plusieurs témoins ou successeurs | Question ouverte ; interface non acquise |
| Quantité structurelle générale | Question ouverte ; interface non acquise |
| Converse d’une reconstruction de trace | Question ouverte ; interface non acquise |
| Fidélité des cibles sous interprétation | Question ouverte ; interface non acquise |
| Nouveau contre-modèle : positivité sans reconstruction intérieure | T2 · deux constructions Lean ; referee IA et contrôle du coordinateur ; vérification humaine en attente |

## Première prochaine exploration

Priorité recommandée : `q.positive-circle`, puis `q.equipped-final-role` et `q.rich-transport`. Construire d’abord les modèles positif et obstrué, expliciter les morphismes équipés, puis demander une nouvelle relecture avant intégration aux sources fondationnelles.

Aucun atlas taille × invariant n’est défini pour ce chantier architectural. `frontier.json` reste absent plutôt que de produire une fraction artificielle de questions résolues.
