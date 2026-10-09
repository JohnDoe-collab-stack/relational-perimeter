# Carte des fondations : relations premières et intérieur constitué

Document généré depuis `knowledge.json` et `sota.json` ; modifier les données, puis régénérer.

Référence formelle : sources relues depuis la base `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685` sur `codex/positive-circular-foundations`. Le snapshot figé conserve ce contexte de revue ; ses empreintes sont recoupées avec les sources actuelles.

Reprise constitutive du 2026-10-09, à partir de la livraison `bf13840cd8f39269a77fa25a3b99260a2930230b`. Elle examine la lecture des résultats sans remplacer leurs preuves.

## Le point de départ

Le projet part des relations témoignées pour constituer les places, les occurrences et le domaine intérieur. Leur identité et leur quantité ne se réduisent pas aux valeurs ou au nombre que l’on peut ensuite lire.

L’intérieur exact est déjà réalisé : deux retours positions–occurrences, liens complets, ordre et succession dans les histoires composables. Un intérieur accompli peut avoir une continuation ; la sortie du régime demande ses propres hypothèses.

Les supports typés sont reçus ; ils ne sont pas le domaine intérieur constitué. Les limites sur des traces plus faibles, des grammaires élargies ou de simples porteurs ne réfutent pas cette constitution. Les généralisations restent annoncées séparément.

Lire [la présentation de la reprise](../docs/priorite-relationnelle-et-perimetre-interieur.fr.md) pour suivre ce que cette priorité change dans l’identité, la quantité, la complétude et la continuation.

58 résultats T2, 14 voies réfutées, 9 questions suivies et 2 pistes T6. Certaines questions sont désormais résolues dans un périmètre précis. Ces nombres ne mesurent pas la part totale de recherche résolue.

Les résultats T2 sont propres au projet. Leur compilation Lean et leur relecture IA sont deux contrôles distincts ; une vérification humaine reste en attente. Les interfaces du plan de reconstruction sont des propositions tant qu’une déclaration précise et sa preuve ne les réalisent pas.

Le plan de reconstruction est désormais versionné. Ses propositions générales restent distinguées des constructions effectivement réalisées ; les anciennes situations de travail sont conservées dans les archives.

Les liens du graphe sont des dépendances sélectionnées et relues. Ils ne sont pas une extraction exhaustive des termes Lean, ni une preuve de nécessité minimale de chaque hypothèse. `supports` exprime un soutien mathématique ; `uses` signale un raccord explicite sélectionné.

## Résultats et hypothèses

### Correspondance exacte positions–occurrences

`th.perimeter-exact` · T2 · refereed

Les positions non fermantes et les occurrences du déploiement canonique se correspondent avec deux lois de retour.

**Hypothèses.** Présentation P et déploiement canonique de sa chaîne successive.

**Preuve consommée.** Inductions et décodage du déploiement ; cette correspondance ne réalise pas finalJunction comme occurrence intérieure.

**Données reçues.** Présentation relationnelle et déploiement canonique de ses jonctions successives.

**Constitution.** Deux applications positions-occurrences et deux retours, avec accords canoniques associés.

**Lectures dérivées.** Les occurrences de ce déploiement sont toutes décodées ; le témoin fermant n'est pas parcouru.

**Portée constitutive.** T2 sur le déploiement intérieur de la même présentation.

**Reprise de l’analyse.** Ce résultat ouvre désormais la lecture : l’intérieur exact est constitué avant sa lecture numérique.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `StrongPerimetralTurning.occurrenceToRequirement_toOccurrence` — [StrongPerimetralTurning.lean:3197](../StrongPerimetralTurning.lean).
- `StrongPerimetralTurning.requirementToOccurrence_toRequirement` — [StrongPerimetralTurning.lean:3205](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Occurrences et positions du déploiement avec deux retours

`th.positive-occurrence-positions` · T2 · refereed

Les occurrences des pas d’une histoire correspondent exactement aux positions non fermantes de son déploiement. L’histoire vide n’a aucune occurrence ; here et later sont distincts dans une même histoire.

**Hypothèses.** PositiveHistory donnée ; occurrences indexées par nil/cons et NonClosingPosition du déploiement.

**Preuve consommée.** Conversion here/later par récursion ; les deux retours par induction ; distinction des constructeurs.

**Portée.** Occurrences de cette nouvelle histoire positive ; aucune identification automatique au générateur historique strict.

**Données reçues.** PositiveHistory de pas concrets et déploiement relationnel.

**Constitution.** Occurrences here/later, vide sans occurrence, distinction des constructeurs et deux retours vers positions.

**Lectures dérivées.** Occurrence et position appartiennent à cette construction ; nœud/état lu ne les identifie pas.

**Portée constitutive.** T2 de la nouvelle formation positive, distinct du générateur strict historique.

**Reprise de l’analyse.** La correspondance constituée est centrale ; elle ne suppose pas l’auto-engendrement de toutes les sortes et de tous les témoins.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.PositiveHistory.nil_noOccurrence` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:152](../RelationalPerimeter/Constitution/PositiveGeneration.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.here_ne_later` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:155](../RelationalPerimeter/Constitution/PositiveGeneration.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.positionTransport` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:194](../RelationalPerimeter/Constitution/PositiveGeneration.lean).

**Relecture.** Referee IA indépendant : lot 2 établi dans la signature de chemins/déploiement ; 38 sondes sans axiomes, données différentes et réindexation vérifiée. Coordinateur : modèles recoupés, build et script global réussis. Vérification humaine en attente.

### Injectivité, ordre et adjacence dans une histoire réelle

`th.rooted-structure` · T2 · refereed

Toute ExactNonClosingRealization dans une RootedGeneratedHistory est injective, conserve la précédence et la succession immédiate.

**Hypothèses.** RootedGeneratedHistory et ExactNonClosingRealization ; à chaque position, accord reçu du seul curseur source avec l’adresse canonique. Les accords des états, de la cible et du pas situé sont ensuite dérivés dans la génération canonique enracinée.

**Preuve consommée.** Trichotomie des occurrences, futurs stricts irréflexifs, accords des curseurs et des états.

**Portée.** Ne vaut pas pour le carrier affaibli SemanticTrace ; adjacence signifie ici succession immédiate.

**Données reçues.** ExactNonClosingRealization dans RootedGeneratedHistory ; seul sourceCursorExact est reçu par l'accord.

**Constitution.** sourceStateExact, locatedStepExact, targetStateExact puis injectivité, précédence et succession immédiate.

**Lectures dérivées.** Le curseur est une adresse structurale dans cette génération canonique ; pas un rang numérique arbitraire.

**Portée constitutive.** T2 spécialisé au générateur historique, à l'enracinement et la composabilité.

**Reprise de l’analyse.** Le seul accord reçu de curseur source est séparé des accords reconstruits d’états et de pas ; les trois résultats sont conservés.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

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

**Données reçues.** Réalisation locale exacte dans une histoire enracinée de pas canoniques.

**Constitution.** Continuation et égalité de recomposition depuis le périmètre canonique.

**Lectures dérivées.** Le suffixe peut être vide ; réalisation de tous les rôles internes ne couvre pas forcément toute histoire cible.

**Portée constitutive.** T2 dans RootedGeneratedHistory ; pas converse de toute trace.

**Reprise de l’analyse.** Confirmer et associer explicitement à la constitution du domaine intérieur ; garder la possibilité du suffixe vide.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `StrongPerimetralTurning.ExactNonClosingRealization.toPerimeterExtension` — [StrongPerimetralTurning.lean:4654](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Grammaire et classification exactes des rôles équipés

`th.equipped-circular-classification` · T2 · refereed

Les rôles intérieurs sont exactement les positions équipées du lien lu ; les rôles circulaires ont une branche intérieure et une branche finale équipée. Classifier vers positions ⊕ Unit puis assembler a deux retours ; les branches sont distinctes.

**Hypothèses.** Même présentation positive P ; lien exactement lu à la position ; rôle final sur closingBoundary P avec témoin exactement choisi.

**Preuve consommée.** Extensionalité du rôle intérieur par sa position et linkExact ; retour canonique ; unicité du rôle final par choix ; élimination des deux constructeurs.

**Portée.** Exhaustivité relative à CircularRole P. Le lien contient les nœuds entiers et leur compatibilité ; aucun rôle arbitraire extérieur ni minimalité universelle classés.

**Données reçues.** Même parent P, position et lien accordés ; rôle final sur choix reçu.

**Constitution.** Rôles canoniques, exactitude position-rôle, grammaire à deux branches et deux retours de classification.

**Lectures dérivées.** Classify oublie le lien/choix au niveau du porteur ; assemble les restitue depuis le même parent.

**Portée constitutive.** T2 exhaustif dans CircularRole P ; aucune troisième branche de ce système.

**Reprise de l’analyse.** Confirmer ; l'exhaustivité déclarée est un acquis de cette construction, pas une théorie d'objets primitivement classifiés.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.EquippedInteriorRole.positionTransport` — [RelationalPerimeter/Constitution/CircularRoles.lean:42](../RelationalPerimeter/Constitution/CircularRoles.lean).
- `RelationalPerimeter.Constitution.EquippedInteriorRole.occurrence_link_readout` — [RelationalPerimeter/Constitution/CircularRoles.lean:66](../RelationalPerimeter/Constitution/CircularRoles.lean).
- `RelationalPerimeter.Constitution.CircularRole.classificationTransport` — [RelationalPerimeter/Constitution/CircularRoles.lean:108](../RelationalPerimeter/Constitution/CircularRoles.lean).
- `RelationalPerimeter.Constitution.CircularRole.exhaustive` — [RelationalPerimeter/Constitution/CircularRoles.lean:115](../RelationalPerimeter/Constitution/CircularRoles.lean).
- `RelationalPerimeter.Constitution.CircularRole.branches_distinct` — [RelationalPerimeter/Constitution/CircularRoles.lean:122](../RelationalPerimeter/Constitution/CircularRoles.lean).

**Relecture.** Referee IA indépendant : sources du lot 4 établies dans leur portée ; 49 sondes sans axiomes, grammaire relative et raccords vérifiés. Coordinateur : brouillons relus/intégrés, modèles compilés, imports publics et vérification globale réussis. Vérification humaine en attente.

### Marqueurs historiques et accords de réalisation

`th.equipped-historical-role-bridge` · T2 · refereed

FinalRequirement et CircularRequirement se raccordent exactement aux rôles équipés du même parent positif. Une réalisation historique reçue lit les positions intérieures, conserve leurs accords concrets et est injective sur les rôles.

**Hypothèses.** Présentation historique P fixée, mêmes périmètre et jonction ; ExactNonClosingRealization P history pour la réalisation.

**Preuve consommée.** Le marqueur singleton est reconstruit depuis le rôle du choix fixé ; retours par unicité ; agreement reçu à la position et realize_injective historique.

**Portée.** La présentation fournit les données oubliées par le marqueur. L’accord est dans Type ; injectivité ne devient pas exhaustivité de toutes les occurrences de l’histoire.

**Données reçues.** Présentation historique fixée ; réalisation exacte de ses positions dans une histoire.

**Constitution.** Transports exacts marqueurs-rôles équipés ; readout concret dans Type ; injectivité de rôles réalisés.

**Lectures dérivées.** Le parent fournit jonction/liens oubliés par les marqueurs ; injectivité ne couvre pas toutes les occurrences cibles.

**Portée constitutive.** T2 du pont sur le même parent et une réalisation reçue.

**Reprise de l’analyse.** Confirmer et rendre visible l'accord équipé ; ne pas juger le rôle complet d'après son seul marqueur singleton.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.HistoricalRoleBridge.finalRequirementTransport` — [RelationalPerimeter/Constitution/HistoricalRoleBridge.lean:8](../RelationalPerimeter/Constitution/HistoricalRoleBridge.lean).
- `RelationalPerimeter.Constitution.HistoricalRoleBridge.marker_junction_readout` — [RelationalPerimeter/Constitution/HistoricalRoleBridge.lean:16](../RelationalPerimeter/Constitution/HistoricalRoleBridge.lean).
- `RelationalPerimeter.Constitution.HistoricalRoleBridge.requirementTransport` — [RelationalPerimeter/Constitution/HistoricalRoleBridge.lean:19](../RelationalPerimeter/Constitution/HistoricalRoleBridge.lean).
- `RelationalPerimeter.Constitution.HistoricalRoleBridge.realization_readout` — [RelationalPerimeter/Constitution/HistoricalRoleBridge.lean:41](../RelationalPerimeter/Constitution/HistoricalRoleBridge.lean).
- `RelationalPerimeter.Constitution.HistoricalRoleBridge.realization_injective` — [RelationalPerimeter/Constitution/HistoricalRoleBridge.lean:47](../RelationalPerimeter/Constitution/HistoricalRoleBridge.lean).

**Relecture.** Referee IA indépendant : sources du lot 4 établies dans leur portée ; 49 sondes sans axiomes, grammaire relative et raccords vérifiés. Coordinateur : brouillons relus/intégrés, modèles compilés, imports publics et vérification globale réussis. Vérification humaine en attente.

### La branche finale ne crée aucune position engendrée

`th.final-role-no-occurrence` · T2 · refereed

La lecture generatedPosition donne some position pour un rôle intérieur et none pour un rôle final. La réalisation historique reçue applique la même distinction : aucune occurrence intérieure n’est attribuée à la branche finale.

**Hypothèses.** Grammaire intérieure/finale déclarée ; réalisation historique exacte reçue pour lire ses occurrences intérieures.

**Preuve consommée.** Lecture par constructeurs dans Option ; impossibilité none = some ; realizeRole final réduit à none.

**Portée.** Absence de position créée par cette branche dans cette classification ; une autre histoire peut contenir une continuation extérieure.

**Données reçues.** Grammaire intérieure/finale ; réalisation historique reçue pour les rôles intérieurs.

**Constitution.** GeneratedPosition some/none et lecture historique finale none.

**Lectures dérivées.** Ce none est une lecture par branche ; il ne prouve pas toute non-réalisation pour une famille RealizesFull future.

**Portée constitutive.** T2 de lecture du système déclaré et de son pont ; continuation autre histoire permise.

**Reprise de l’analyse.** Confirmer en reliant à l'intérieur couvert exactement ; ne pas transformer absence d'attribution en nécessité universelle de toutes les relations.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.CircularRole.generatedPosition` — [RelationalPerimeter/Constitution/CircularRoles.lean:128](../RelationalPerimeter/Constitution/CircularRoles.lean).
- `RelationalPerimeter.Constitution.CircularRole.final_not_interior_position` — [RelationalPerimeter/Constitution/CircularRoles.lean:138](../RelationalPerimeter/Constitution/CircularRoles.lean).
- `RelationalPerimeter.Constitution.HistoricalRoleBridge.final_not_realized` — [RelationalPerimeter/Constitution/HistoricalRoleBridge.lean:59](../RelationalPerimeter/Constitution/HistoricalRoleBridge.lean).

**Relecture.** Referee IA indépendant : sources du lot 4 établies dans leur portée ; 49 sondes sans axiomes, grammaire relative et raccords vérifiés. Coordinateur : brouillons relus/intégrés, modèles compilés, imports publics et vérification globale réussis. Vérification humaine en attente.

### Lecture numérique dérivée des histoires

`th.numeric-readout` · T2 · refereed

Une histoire perimétralement admissible a une longueur inférieure ou égale à celle du déploiement canonique.

**Hypothèses.** PerimetrallyAdmissible P history, soit une partie libre soit un raffinement du même périmètre.

**Preuve consommée.** admissible_is_prefix_of_perimeter et monotonie de History.length sur les préfixes.

**Portée.** History.length compte les pas après leur constitution. La quantité intérieure exacte est déjà portée par les deux retours positions–occurrences et leurs accords structuraux ; la longueur ne constitue ni l’identité ni les relations des occurrences.

**Données reçues.** Histoire PerimetrallyAdmissible du même périmètre.

**Constitution.** Préfixe constitué puis monotonie de History.length et borne numérique.

**Lectures dérivées.** Le naturel oublie identité, liens et témoins ; il ne définit pas les occurrences ni leur ordre.

**Portée constitutive.** T2 de lecture dérivée ; pas définition primitive de quantité structurelle.

**Reprise de l’analyse.** Confirmer et remplacer tout récit cardinal premier par constitution du domaine exact suivie de sa mesure.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `StrongPerimetralTurning.admissible_length_le_perimeter` — [StrongPerimetralTurning.lean:7138](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Présentation positive et obstruction séparées

`th.positive-split` · T2 · refereed

Les données circulaires positives sont définies sans rejet de contraction. Une même chaîne reçoit des lectures de pôles identifiés ou séparés ; seule la seconde reçoit l’obstruction de l’exemple.

**Hypothèses.** Chaîne positive et jonction reçues en entrée ; séparation dérivée seulement avec CircularClosureObstruction.

**Preuve consommée.** Le modèle Unit identifie les pôles ; l’obstruction Bool rejetant false = true enrichit le même parent positif.

**Portée.** Aucune algèbre générale d’engendrement, ni boucle d’exécution historique périodique.

**Données reçues.** Épine, témoins et jonction ; lectures de pôles Unit ou Bool.

**Constitution.** Parent positif commun et enrichissement obstrué sur la lecture séparée.

**Lectures dérivées.** La lecture identifiée ne porte pas cette obstruction ; même chaîne ne signifie pas mêmes pôles.

**Portée constitutive.** T2 sur couches positives et obstruction explicites.

**Reprise de l’analyse.** Confirmer ; le résultat sépare circularité positive et choix d'obstruction, pas périodicité d'une génération.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `StrongPerimetralTurning.PositiveCircularPresentation` — [RelationalPerimeter/Constitution/PositivePresentation.lean:18](../RelationalPerimeter/Constitution/PositivePresentation.lean).
- `StrongPerimetralTurning.CircularClosureObstruction.endpointsSeparated` — [RelationalPerimeter/Constitution/PositivePresentation.lean:62](../RelationalPerimeter/Constitution/PositivePresentation.lean).
- `RelationalPerimeter.Constitution.Examples.identifiedBoundary_no_obstruction` — [RelationalPerimeter/Constitution/Examples.lean:46](../RelationalPerimeter/Constitution/Examples.lean).
- `RelationalPerimeter.Constitution.Examples.same_positive_data` — [RelationalPerimeter/Constitution/Examples.lean:68](../RelationalPerimeter/Constitution/Examples.lean).

**Relecture.** Énoncé et portée relus par un referee IA indépendant ; sondes propres sur cinq porteurs et deux échanges distincts. Build complet et contrôle constructif par le coordinateur. Vérification humaine en attente.

### Déploiement depuis une formation positive reçue

`th.positive-formation-deployment` · T2 · refereed

Une formation reçoit états, nœuds et pas admissibles avec leur compatibilité. Toute histoire finie composable déploie une épine conservant le départ, le terme et les paquets de nœuds/compatibilité lus à chaque pas.

**Hypothèses.** PositiveFormation, nœuds déjà témoins, Step indexé et compatibility(step) ; histoire de pas concrets.

**Preuve consommée.** Récursion nil/cons ; égalité du nœud terminal par induction ; deploy_link_exact conserve le paquet SuccessiveLink entier.

**Portée.** Les pas et primitives sont reçus. Le déploiement peut oublier des données supplémentaires de Step ; aucune injectivité générale sur les histoires.

**Données reçues.** PositiveFormation, State/node/Step et compatibilité des pas concrets.

**Constitution.** Déploiement récursif, départ/terme exacts et lien complet conservé à chaque occurrence.

**Lectures dérivées.** L'épine garde nœuds et compatibilités ; elle peut oublier du contenu supplémentaire de Step.

**Portée constitutive.** T2 relatif à la formation ; pas injectivité générale de deploy.

**Reprise de l’analyse.** Les occurrences sont constituées à partir de pas témoins ; recevoir des nœuds équipés ne revient pas à recevoir ces occurrences déjà individuées.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

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

**Portée.** L’accord d’indices fait partie du théorème. La propriété universelle des chemins reste ouverte. Le transport des opérations est réalisé au lot 3 pour la formation reconstruite, sans comparaison de formations cibles arbitraires.

**Données reçues.** Deux histoires aux états intermédiaires communs.

**Constitution.** Deux unités, associativité et déploiement de append par appendAlong.

**Lectures dérivées.** L'accord terminal réindexe le suffixe ; égalité de valeur numérique ne fournit aucun raccord.

**Portée constitutive.** T2 d'opérations dans une formation fixée.

**Reprise de l’analyse.** La propriété universelle reste ouverte ; les transports des opérations réalisés séparément au lot 3 sont maintenant signalés.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.PositiveHistory.nil_append` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:105](../RelationalPerimeter/Constitution/PositiveGeneration.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.append_nil` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:108](../RelationalPerimeter/Constitution/PositiveGeneration.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.append_associative` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:115](../RelationalPerimeter/Constitution/PositiveGeneration.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.deploy_append` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:137](../RelationalPerimeter/Constitution/PositiveGeneration.lean).

**Relecture.** Referee IA indépendant : lot 2 établi dans la signature de chemins/déploiement ; 38 sondes sans axiomes, données différentes et réindexation vérifiée. Coordinateur : modèles recoupés, build et script global réussis. Vérification humaine en attente.

### Clôture explicite du déploiement positif

`th.positive-explicit-closing` · T2 · refereed

Une histoire extrait une forme de frontière sans jonction. Une occurrence et une jonction concrète permettent ensuite de construire une présentation positive conservant le nœud initial, le déploiement, la jonction et la frontière équipée.

**Hypothèses.** Occurrence history dans Type et ClosingWitness history.boundaryShape, fournis séparément.

**Preuve consommée.** boundary_source_exact dérive la lecture terminale ; toCircular lit les champs de la même histoire et les deux données fournies.

**Portée.** La positivité seule ne construit aucune jonction ; aucune extraction depuis une existence propositionnelle.

**Données reçues.** Histoire, occurrence positive dans Type et jonction dans ClosingWitness séparément.

**Constitution.** Forme de frontière puis présentation positive avec quatre accords.

**Lectures dérivées.** Source terminale lue par deploy_final ; positivité n'habite pas la fibre fermante à elle seule.

**Portée constitutive.** T2 de fermeture explicite d'une histoire positive.

**Reprise de l’analyse.** Confirmer ; cette réception de jonction n'est pas un défaut de constitution des places intérieures.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

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

**Données reçues.** Histoire positive, jonction, pôles et obstruction sur sa présentation déployée.

**Constitution.** CircularPresentation et accords exacts des trois couches/déploiement.

**Lectures dérivées.** La génération positive ne consomme pas le rejet ; le pont le fournit aux interfaces historiques.

**Portée constitutive.** T2 de raccord sur le même parent ; pas no-return de tout Step.

**Reprise de l’analyse.** Confirmer avec séparation entre histoire générique, parent positif et génération canonique historique.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

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

**Données reçues.** ChosenPositiveContinuation fournit successor et pas depuis chaque état ; modèles dirigé/ramifié.

**Constitution.** Walk fini positif ; modèles à deux successeurs ou sans choix global.

**Lectures dérivées.** Count pilote une itération choisie, pas l'identité des occurrences ni le cardinal primitif du domaine.

**Portée constitutive.** T2 sous choix ; non-existence globale permise dans une formation.

**Reprise de l’analyse.** Confirmer ; l'architecture générique est relationnelle sans imposer déterminisme ou totalité.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.ChosenPositiveContinuation.walk` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:270](../RelationalPerimeter/Constitution/PositiveGeneration.lean).
- `RelationalPerimeter.Constitution.ChosenPositiveContinuation.walk_successor_positive` — [RelationalPerimeter/Constitution/PositiveGeneration.lean:277](../RelationalPerimeter/Constitution/PositiveGeneration.lean).
- `RelationalPerimeter.Constitution.PositiveGenerationExamples.branching_targets_distinct` — [RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:129](../RelationalPerimeter/Constitution/PositiveGenerationExamples.lean).
- `RelationalPerimeter.Constitution.PositiveGenerationExamples.chosen_successors_distinct` — [RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:141](../RelationalPerimeter/Constitution/PositiveGenerationExamples.lean).
- `RelationalPerimeter.Constitution.PositiveGenerationExamples.directed_no_global_continuation` — [RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:52](../RelationalPerimeter/Constitution/PositiveGenerationExamples.lean).

**Relecture.** Referee IA indépendant : lot 2 établi dans la signature de chemins/déploiement ; 38 sondes sans axiomes, données différentes et réindexation vérifiée. Coordinateur : modèles recoupés, build et script global réussis. Vérification humaine en attente.

### Reconstruction exacte de la présentation historique

`th.circular-bridge` · T2 · refereed

Extraire la présentation positive, la frontière de pôles et l’obstruction puis les réassembler reconstruit exactement CircularPresentation ; les trois couches ont aussi leurs lois de retour.

**Hypothèses.** Présentation historique, ou présentation positive équipée d’une frontière et d’une obstruction.

**Preuve consommée.** Les quatre retours sont établis par réduction et analyse de structure ; tous les champs et témoins sont conservés.

**Portée.** Le pont conserve l’interface historique consommée par les preuves et la partie computationnelle.

**Données reçues.** Présentation positive, lectures de pôles et obstruction ou présentation historique.

**Constitution.** Réassemblage et quatre retours exacts de toutes les couches.

**Lectures dérivées.** Extraction/reconstruction préserve champs et témoins ; pas nouvelle architecture concurrente.

**Portée constitutive.** T2 de pont exact ; consommateurs computationnels seulement situés.

**Reprise de l’analyse.** Confirmer les retours ; ne pas traiter ce pont comme validation de toute application computationnelle.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

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

**Données reçues.** Présentation positive déjà pointée par finalJunction.

**Constitution.** ConstitutiveBoundary avec indices, jonction, différence et provenance sélectionnés.

**Lectures dérivées.** Extraction de données autoritatives ; pas occurrence nouvelle et pas signature universelle.

**Portée constitutive.** T2 de frontière sélectionnée du même parent.

**Reprise de l’analyse.** Extraction présentée après la description de l’intérieur dans l’exposition ; closingBoundary ne dépend pas d’une réalisation en occurrences. Ses données reçues ne réfutent pas leur constitution relationnelle.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.closingBoundary` — [RelationalPerimeter/Constitution/BoundaryTransport.lean:31](../RelationalPerimeter/Constitution/BoundaryTransport.lean).
- `PositiveFoundationReferee.extractedBoundaryReadsExactData` — [research/agents/referee-positive-foundations/IndependentProbes.lean.in:145](../research/agents/referee-positive-foundations/IndependentProbes.lean.in).

**Relecture.** Énoncé et portée relus par un referee IA indépendant ; sondes propres sur cinq porteurs et deux échanges distincts. Build complet et contrôle constructif par le coordinateur. Vérification humaine en attente.

### Frontière sans jonction et reconstruction exacte

`th.closing-shape-bridge` · T2 · refereed

ClosingBoundaryShape omet seulement la jonction. Un pointage indexé fournit ce témoin ; oubli et reconstruction ont des retours exacts pour la forme, le pointage et la ConstitutiveBoundary actuelle.

**Hypothèses.** Sortes, familles, source/cible, différence et provenance initiales sélectionnées ; jonction fournie pour reconstruire la frontière équipée.

**Preuve consommée.** Les champs sont copiés directement ; les trois retours sont obtenus par réduction et analyse du pointage.

**Portée.** La provenance et les indices restent choisis ; aucune minimalité universelle de signature.

**Données reçues.** Sortes/familles, indices, différence et provenance choisis.

**Constitution.** Oubli de la jonction, pointage et réassemblage avec trois retours exacts.

**Lectures dérivées.** Oublier jonction conserve les autres choix ; pas signature sans données distinguées.

**Portée constitutive.** T2 de frontière sélectionnée avant/après pointage.

**Reprise de l’analyse.** Confirmer ; ne pas présenter la forme comme génération de toutes ses sortes et indices.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

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

**Données reçues.** Forme B et terme ClosingWitness pour point ; Nonempty seulement pour existence.

**Constitution.** Transport exact témoin-pointage et équivalence propositionnelle d'habitation.

**Lectures dérivées.** Nonempty n'est éliminé que vers Prop ; ne fournit pas une fonction de choix vers Type.

**Portée constitutive.** T2 de fibre fermante et enrichissement indexé.

**Reprise de l’analyse.** Confirmer existence/choix/donnée séparés ; ne pas confondre l'absence de choix automatique avec absence de relation primitive.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

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

**Données reçues.** Forme directe avec ClosingWitness vide, indices et provenance disponibles.

**Constitution.** Impossibilité de pointage et rôle sur un choix ; impossibilité de provenir d'une frontière déjà équipée.

**Lectures dérivées.** L'oubli d'un témoin existant conserve une habitation ; modèle vide doit être construit avant pointage.

**Portée constitutive.** T2 d'un modèle préalable à clôture.

**Reprise de l’analyse.** Le modèle précise une limite avant choix ; il ne s’applique pas à une présentation déjà munie de sa jonction fermante.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

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

**Portée.** Aucune unicité de tous les pointages ni occurrence nouvelle engendrée. Ce nœud concerne le rôle sur un choix fixé ; la classification relative des rôles est réalisée séparément au lot 4, et la rigidité générale reste ouverte.

**Données reçues.** PointedClosingBoundary et jonction concrète.

**Constitution.** Habitant du rôle, unicité et accord exact du témoin avec cette jonction.

**Lectures dérivées.** Habitation du couple choix/rôle est propositionnelle ; aucun choix global unique déduit.

**Portée constitutive.** T2 par pointage, pas sur tous les pointages d'une forme.

**Reprise de l’analyse.** Confirmer et préciser la quantification sur le choix, sans confondre rôle et jonction.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

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

**Données reçues.** Modèles de fibres Unit/Bool ; pointages false et true.

**Constitution.** Unicité de témoin Unit, deux pointages Bool distincts et rôle unique sur chacun.

**Lectures dérivées.** L'unicité de chaque fibre de rôle ne fusionne pas les choix à l'échelle de la forme.

**Portée constitutive.** T2 de modèles précis ; pas classification universelle des frontières.

**Reprise de l’analyse.** Confirmer ; la multiplicité reçue est compatible avec la priorité relationnelle.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.ClosingBoundaryExamples.unit_fibre_unique` — [RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean:50](../RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean).
- `RelationalPerimeter.Constitution.ClosingBoundaryExamples.bool_pointings_distinct` — [RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean:70](../RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean).
- `RelationalPerimeter.Constitution.ClosingBoundaryExamples.bool_per_choice_role_unique` — [RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean:84](../RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean).
- `RelationalPerimeter.Constitution.ClosingBoundaryExamples.bool_closing_fibre_not_unique` — [RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean:95](../RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean).

**Relecture.** Referee IA indépendant : lot 1 établi dans sa portée, propres sondes à fibres dépendantes et données sélectionnées distinctes ; 20 audits sans axiomes. Coordinateur : modèles recoupés, build complet et contrôle global réussis. Vérification humaine en attente.

### Accord des applications directes et unicité de l’inverse

`th.transport-backward` · T2 · refereed

Deux ExactTypeTransport dont les fonctions directes coïncident point par point ont des fonctions inverses qui coïncident point par point.

**Hypothèses.** Deux applications dans chaque sens et leurs lois de retour ; accord ponctuel des fonctions directes.

**Preuve consommée.** Lois de retour des deux transports et forwardAgreement.

**Portée.** Le transport exact entre porteurs ne contient pas d’accord relationnel supplémentaire.

**Données reçues.** Deux transports exacts et accord ponctuel des cartes directes.

**Constitution.** Accord ponctuel de leurs cartes inverses.

**Lectures dérivées.** Les porteurs sont comparés ; aucune conservation relationnelle n'est incluse par défaut.

**Portée constitutive.** T2 neutre, appliqué ensuite aux interfaces équipées.

**Reprise de l’analyse.** Confirmer ; ne pas confondre cet oubli des relations avec la nature fondationnelle des objets comparés.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `ExactTypeTransport.backward_eq_of_forward_eq` — [ExactTypeTransport.lean:101](../ExactTypeTransport.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Calcul constructif des transports équipés de frontière

`th.boundary-calculus` · T2 · refereed

Les transports exacts des cinq porteurs conservant trois indices et deux témoins sont fermés par identité, inversion et composition. Unités, associativité et inverses valent point par point ; l’accord inverse se déduit de l’accord direct.

**Hypothèses.** Cinq ExactTypeTransport ; sourceExact, targetExact, differenceExact, junctionExact et provenanceExact.

**Preuve consommée.** Inversion par lois de retour et congrArg ; composition des cinq accords ; égalité inverse par backward_eq_of_forward_eq.

**Portée.** Fibres de compatibilité et provenance sélectionnées seulement ; aucune égalité globale de structures de fonctions.

**Données reçues.** Cinq transports exacts et cinq accords d'indices/témoins distingués.

**Constitution.** Identité, inversion, composition, lois pointwise et accord inverse dérivé.

**Lectures dérivées.** Seules fibres sélectionnées et choix sont comparés ; aucune égalité globale de fonctions.

**Portée constitutive.** T2 de signature sélectionnée avec lois explicites.

**Reprise de l’analyse.** Confirmer ; conserver distinction cartes réversibles et préservation des choix.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

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

**Portée.** La fibre est contractile, indexée par une frontière choisie. Son porteur seul ne détermine pas les morphismes riches ; la grammaire complète est traitée séparément par th.equipped-circular-classification.

**Données reçues.** Frontière déjà pointée ; témoin accordé ; BoundaryTransport riche pour changer de frontière.

**Constitution.** Habitant canonique, unicité par choix et transport exact avec conservation des vues.

**Lectures dérivées.** Source/cible/provenance sont lues sur l'index ; singleton nu ne décrit pas les lois du morphisme riche.

**Portée constitutive.** T2 sur une frontière équipée fixe ; grammaire complète acquise ailleurs.

**Reprise de l’analyse.** Le rôle final sur le choix fixé est acquis ; la note renvoie désormais à la grammaire complète relative du lot 4.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

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

### Transports exacts de chaque fibre relationnelle

`th.signature-fibre-transport` · T2 · refereed

Chaque paire implicite/explicite et chaque différence reçoit deux applications avec deux retours, aux indices transportés. La signature ne se limite plus aux fibres sélectionnées par une frontière.

**Hypothèses.** ConstitutiveSignatureTransport reçoit les trois transports des sortes et tous les transports exacts de fibres.

**Preuve consommée.** Applications et retours reçus dans ExactTypeTransport ; les indices des fibres cibles sont les images des indices sources.

**Portée.** Les transports relationnels sont des données concrètes ; aucune dérivation depuis les seules bijections des sortes.

**Données reçues.** Trois cartes de sortes et transports exacts de chaque fibre aux indices images.

**Constitution.** Vues directes/inverses et retours de toutes les compatibilités et provenances.

**Lectures dérivées.** Les cartes relationnelles sont reçues, pas déduites des cartes de supports.

**Portée constitutive.** T2 relatif à cette signature explicite ; pas toute signature dépendante.

**Reprise de l’analyse.** Confirmer ; les sorts typés ne sont pas des unités d'intérieur, et leur exactitude ne suffit pas aux relations.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.compatibility_return` — [RelationalPerimeter/Constitution/SignatureTransport.lean:92](../RelationalPerimeter/Constitution/SignatureTransport.lean).
- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.compatibility_return_target` — [RelationalPerimeter/Constitution/SignatureTransport.lean:97](../RelationalPerimeter/Constitution/SignatureTransport.lean).
- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.provenance_return` — [RelationalPerimeter/Constitution/SignatureTransport.lean:103](../RelationalPerimeter/Constitution/SignatureTransport.lean).
- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.provenance_return_target` — [RelationalPerimeter/Constitution/SignatureTransport.lean:108](../RelationalPerimeter/Constitution/SignatureTransport.lean).

**Relecture.** Referee IA indépendant : sources du lot 3 établies dans leur portée ; 62 sondes sans axiomes, fibres variables et closing Empty vérifiées. Coordinateur : brouillons d’auteur relus et compilés, modèles recoupés, imports publics et contrôle global réussis. Vérification humaine en attente.

### Calcul dépendant des transports complets

`th.signature-calculus` · T2 · refereed

Identité, inversion, composition, unités gauche/droite et associativité des applications de fibres sont réalisés. Les retours d’inversion exposent les réindexations par les lois de retour des sortes.

**Hypothèses.** Transports exacts de signatures ; compatibilityAt et provenanceAt réindexent les fibres cibles nommées.

**Preuve consommée.** Composition lit le second transport aux images du premier. Inversion réindexe avant la carte inverse ; backward_reindex par élimination des égalités et retours exacts.

**Portée.** Lois point par point, pas égalité globale des structures de fonctions ; aucune extension aux opérations de pôles.

**Données reçues.** Transports exacts de signatures et égalités de réindexation.

**Constitution.** Identité, inversion, composition, lois pointwise et retours avec reindex explicite.

**Lectures dérivées.** Aucune égalité globale de structures de fonctions ni opération de pôle conservée.

**Portée constitutive.** T2 du calcul de cette signature.

**Reprise de l’analyse.** Confirmer les lois ; ne pas appeler absence de signature universelle absence de comparaison relationnelle.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.identity_left_compatibility` — [RelationalPerimeter/Constitution/SignatureTransport.lean:145](../RelationalPerimeter/Constitution/SignatureTransport.lean).
- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.identity_right_compatibility` — [RelationalPerimeter/Constitution/SignatureTransport.lean:150](../RelationalPerimeter/Constitution/SignatureTransport.lean).
- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.identity_left_provenance` — [RelationalPerimeter/Constitution/SignatureTransport.lean:155](../RelationalPerimeter/Constitution/SignatureTransport.lean).
- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.identity_right_provenance` — [RelationalPerimeter/Constitution/SignatureTransport.lean:159](../RelationalPerimeter/Constitution/SignatureTransport.lean).
- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.compose_associative_compatibility` — [RelationalPerimeter/Constitution/SignatureTransport.lean:163](../RelationalPerimeter/Constitution/SignatureTransport.lean).
- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.compose_associative_provenance` — [RelationalPerimeter/Constitution/SignatureTransport.lean:170](../RelationalPerimeter/Constitution/SignatureTransport.lean).
- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.reverse_compatibility_return` — [RelationalPerimeter/Constitution/SignatureTransport.lean:194](../RelationalPerimeter/Constitution/SignatureTransport.lean).
- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.reverse_provenance_return` — [RelationalPerimeter/Constitution/SignatureTransport.lean:204](../RelationalPerimeter/Constitution/SignatureTransport.lean).
- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.reverse_compatibility_return_target` — [RelationalPerimeter/Constitution/SignatureTransport.lean:212](../RelationalPerimeter/Constitution/SignatureTransport.lean).
- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.reverse_provenance_return_target` — [RelationalPerimeter/Constitution/SignatureTransport.lean:218](../RelationalPerimeter/Constitution/SignatureTransport.lean).

**Relecture.** Referee IA indépendant : sources du lot 3 établies dans leur portée ; 62 sondes sans axiomes, fibres variables et closing Empty vérifiées. Coordinateur : brouillons d’auteur relus et compilés, modèles recoupés, imports publics et contrôle global réussis. Vérification humaine en attente.

### Restriction complète vers la frontière choisie

`th.signature-boundary-restriction` · T2 · refereed

Les transports complets se restreignent aux cinq porteurs sélectionnés. Trois accords d’indices puis deux accords des témoins choisis construisent exactement BoundaryTransport.

**Hypothèses.** sourceExact, targetExact, differenceExact puis junctionExact et provenanceExact pour les témoins distingués.

**Preuve consommée.** restrictCarriers utilise compatibilityAt/provenanceAt ; restrict conserve les cartes ainsi restreintes et reçoit les accords manquants.

**Portée.** Les échanges de jonction/provenance peuvent conserver toutes les familles sans conserver les témoins choisis. Exactitude des familles ne remplace pas ces deux accords.

**Données reçues.** Transports complets ; accords source/cible/différence puis jonction/provenance.

**Constitution.** Restriction des familles aux cinq porteurs et construction de BoundaryTransport.

**Lectures dérivées.** Exactitude de toutes les fibres ne fixe pas automatiquement leurs témoins distingués.

**Portée constitutive.** T2 de restriction à mêmes données choisies sous accords explicites.

**Reprise de l’analyse.** Confirmer ; distinguer transport de relation et conservation de son témoin choisi.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.restrict` — [RelationalPerimeter/Constitution/SignatureTransport.lean:251](../RelationalPerimeter/Constitution/SignatureTransport.lean).
- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.restrict_junction_forward` — [RelationalPerimeter/Constitution/SignatureTransport.lean:266](../RelationalPerimeter/Constitution/SignatureTransport.lean).
- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.restrict_provenance_backward` — [RelationalPerimeter/Constitution/SignatureTransport.lean:274](../RelationalPerimeter/Constitution/SignatureTransport.lean).
- `RelationalPerimeter.Constitution.SignatureTransportExamples.selectedRestriction` — [RelationalPerimeter/Constitution/SignatureTransportExamples.lean:99](../RelationalPerimeter/Constitution/SignatureTransportExamples.lean).

**Relecture.** Referee IA indépendant : sources du lot 3 établies dans leur portée ; 62 sondes sans axiomes, fibres variables et closing Empty vérifiées. Coordinateur : brouillons d’auteur relus et compilés, modèles recoupés, imports publics et contrôle global réussis. Vérification humaine en attente.

### Transport des nœuds, épines et lectures de liens

`th.signature-spine-transport` · T2 · refereed

Le transport complet construit les nœuds et chaque avancée. Il raccorde le terme, les liens et la composition avec réindexation du suffixe par le même terme.

**Hypothèses.** Transport de toutes les fibres ; épine source donnée, suffixe indexé par son nœud terminal réel.

**Preuve consommée.** Récursion sur boundary/advance, transport des compatibilités et provenances de tous les nœuds ; induction pour final et appendAlong.

**Portée.** Transport d’une épine source, sans empaquetage d’une équivalence générique entre tous les types d’épines.

**Données reçues.** Signature transportée fibre par fibre et épine source témoignées.

**Constitution.** mapNode/mapSpine, accord du terme, lien complet et composition réindexée.

**Lectures dérivées.** Pas de paquet d'équivalence générique de toutes les épines ; cette restriction ne retire pas le transport donné.

**Portée constitutive.** T2 d'une épine source vers son image.

**Reprise de l’analyse.** Confirmer et mettre en avant les témoins internes et successifs conservés dans chaque nœud/lien.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.mapSpine_final` — [RelationalPerimeter/Constitution/SpineTransport.lean:24](../RelationalPerimeter/Constitution/SpineTransport.lean).
- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.mapSpine_append` — [RelationalPerimeter/Constitution/SpineTransport.lean:31](../RelationalPerimeter/Constitution/SpineTransport.lean).
- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.mapSpine_link` — [RelationalPerimeter/Constitution/SpineTransport.lean:156](../RelationalPerimeter/Constitution/SpineTransport.lean).

**Relecture.** Referee IA indépendant : sources du lot 3 établies dans leur portée ; 62 sondes sans axiomes, fibres variables et closing Empty vérifiées. Coordinateur : brouillons d’auteur relus et compilés, modèles recoupés, imports publics et contrôle global réussis. Vérification humaine en attente.

### Positions exactes, précédence et succession conservées et réfléchies

`th.signature-position-order` · T2 · refereed

Sur une épine source fixée, positions et positions de son image ont deux retours exacts. Précédence et succession immédiate sont chacune préservées et réfléchies.

**Hypothèses.** Épine donnée, applications récursives de positions, constructeurs distincts NonClosingPrecedes et NonClosingNext.

**Preuve consommée.** Récursion here/later ; retours des positions ; induction des relations et restauration structurale.

**Portée.** La conservation de relations est prouvée séparément de la bijection ; la répétition de nœuds bruts ne fusionne pas les positions.

**Données reçues.** Épine fixée, cartes récursives, relations structurales Precedes et Next.

**Constitution.** Deux retours de positions ; préservation/réflexion de précédence et succession immédiate.

**Lectures dérivées.** La bijection de positions seule ne prouve pas ces relations ; preuves séparées sur leurs constructeurs.

**Portée constitutive.** T2 sur l'épine source et son image.

**Reprise de l’analyse.** Confirmer ; rattacher directement à quantité intérieure et à l'identité des positions malgré nœuds répétés.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.positionTransport` — [RelationalPerimeter/Constitution/SpineTransport.lean:75](../RelationalPerimeter/Constitution/SpineTransport.lean).
- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.precedes_iff` — [RelationalPerimeter/Constitution/SpineTransport.lean:128](../RelationalPerimeter/Constitution/SpineTransport.lean).
- `RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.next_iff` — [RelationalPerimeter/Constitution/SpineTransport.lean:139](../RelationalPerimeter/Constitution/SpineTransport.lean).

**Relecture.** Referee IA indépendant : sources du lot 3 établies dans leur portée ; 62 sondes sans axiomes, fibres variables et closing Empty vérifiées. Coordinateur : brouillons d’auteur relus et compilés, modèles recoupés, imports publics et contrôle global réussis. Vérification humaine en attente.

### Reconstruction de formation et histoires entières exactes

`th.signature-formation-histories` · T2 · refereed

Une formation transportée conserve littéralement ses états et ses types de pas entiers. Ses nœuds et lectures relationnelles sont transportés. Histoires et occurrences ont deux applications avec deux retours exacts.

**Hypothèses.** Formation F et transport de F.signature ; formation cible définie par F.transport, mêmes State et Step.

**Preuve consommée.** Reconstruction des champs ; transport/restauration par nil/cons avec le même pas concret ; deux retours par induction.

**Portée.** Données supplémentaires de Step conservées dans l’histoire. Aucune comparaison exacte de formations cibles arbitraires ; le déploiement ne reconstruit pas ces données.

**Données reçues.** Formation source et transport de sa signature ; State et Step entiers conservés.

**Constitution.** Formation cible reconstruite ; deux cartes d'histoires/occurrences avec deux retours.

**Lectures dérivées.** Données supplémentaires de Step conservées dans histoires ; deploy peut les oublier.

**Portée constitutive.** T2 pour F.transport, pas formation cible arbitraire préexistante.

**Reprise de l’analyse.** Confirmer avec même State/Step explicités ; le résultat est riche malgré cette borne de généralité.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.PositiveFormation.transport` — [RelationalPerimeter/Constitution/FormationTransport.lean:28](../RelationalPerimeter/Constitution/FormationTransport.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.signatureTransport` — [RelationalPerimeter/Constitution/FormationTransport.lean:131](../RelationalPerimeter/Constitution/FormationTransport.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.occurrenceSignatureTransport` — [RelationalPerimeter/Constitution/FormationTransport.lean:208](../RelationalPerimeter/Constitution/FormationTransport.lean).

**Relecture.** Referee IA indépendant : sources du lot 3 établies dans leur portée ; 62 sondes sans axiomes, fibres variables et closing Empty vérifiées. Coordinateur : brouillons d’auteur relus et compilés, modèles recoupés, imports publics et contrôle global réussis. Vérification humaine en attente.

### Formation, composition et déploiement commutants

`th.signature-formation-operations` · T2 · refereed

Transport des histoires et composition commutent ; déployer après transport donne l’épine transportée. Les positions et leurs relations, les liens et la marche choisie ont les raccords correspondants.

**Hypothèses.** Formation reconstruite, histoires composables ; continuation déjà choisie pour walk.

**Preuve consommée.** Induction sur l’histoire et la marche ; transport_position expose le cast de l’accord de déploiement ; relations via les équivalences de l’épine.

**Portée.** Le successeur et le pas choisi restent ceux reçus ; aucune disponibilité générale ou détermination du successeur.

**Données reçues.** Histoires composables, reconstruction F.transport et continuation déjà choisie pour walk.

**Constitution.** Carrés append/deploy, positions, ordre, succession, liens et itération.

**Lectures dérivées.** Successor et pas choisi restent reçus ; la reconstruction ne crée aucune disponibilité globale.

**Portée constitutive.** T2 d'opérations sur formation reconstruite.

**Reprise de l’analyse.** Confirmer et utiliser ces acquis pour une future interface de quantité au lieu de les annoncer manquants.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.PositiveHistory.transport_append` — [RelationalPerimeter/Constitution/FormationTransport.lean:140](../RelationalPerimeter/Constitution/FormationTransport.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.transport_deploy` — [RelationalPerimeter/Constitution/FormationTransport.lean:151](../RelationalPerimeter/Constitution/FormationTransport.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.transport_position` — [RelationalPerimeter/Constitution/FormationTransport.lean:217](../RelationalPerimeter/Constitution/FormationTransport.lean).
- `RelationalPerimeter.Constitution.ChosenPositiveContinuation.transport_walk` — [RelationalPerimeter/Constitution/FormationTransport.lean:309](../RelationalPerimeter/Constitution/FormationTransport.lean).

**Relecture.** Referee IA indépendant : sources du lot 3 établies dans leur portée ; 62 sondes sans axiomes, fibres variables et closing Empty vérifiées. Coordinateur : brouillons d’auteur relus et compilés, modèles recoupés, imports publics et contrôle global réussis. Vérification humaine en attente.

### Clôture et frontière équipée de la chaîne transportée

`th.signature-closing-transport` · T2 · refereed

La fibre fermante de l’histoire et celle de son image ont un transport exact. Une jonction reçue construit une présentation positive transportée et un BoundaryTransport conservant les cinq données choisies.

**Hypothèses.** Histoire, occurrence et jonction reçues ; reconstruction de formation et transport de signature complet.

**Preuve consommée.** Accord source via déploiement et terme ; compatibilityAt réindexe la fibre ; restrict reçoit les cinq accords calculés des deux frontières.

**Portée.** Une fibre fermante vide reste sans jonction cible. Ce module transporte le rôle final actuel ; la classification complète et ses transports sont traités séparément au lot 4. Pôles et obstruction restent hors de cette interface.

**Données reçues.** Histoire, occurrence positive, jonction et transport complet de signature.

**Constitution.** Transport exact de fibre fermante, parent circulaire cible et frontière avec cinq accords.

**Lectures dérivées.** Une fibre vide reste sans jonction ; les pôles et leur obstruction ne sont pas transportés.

**Portée constitutive.** T2 sur reconstruction ; grammaire des rôles désormais acquise dans lot 4.

**Reprise de l’analyse.** La clôture et sa frontière équipée sont distinguées de la classification des rôles, réalisée séparément au lot 4.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.PositiveHistory.closingSignatureTransport` — [RelationalPerimeter/Constitution/ClosingTransport.lean:18](../RelationalPerimeter/Constitution/ClosingTransport.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.circularBoundaryTransport` — [RelationalPerimeter/Constitution/ClosingTransport.lean:45](../RelationalPerimeter/Constitution/ClosingTransport.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.circular_junction_preserved` — [RelationalPerimeter/Constitution/ClosingTransport.lean:55](../RelationalPerimeter/Constitution/ClosingTransport.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.circular_provenance_preserved` — [RelationalPerimeter/Constitution/ClosingTransport.lean:62](../RelationalPerimeter/Constitution/ClosingTransport.lean).

**Relecture.** Referee IA indépendant : sources du lot 3 établies dans leur portée ; 62 sondes sans axiomes, fibres variables et closing Empty vérifiées. Coordinateur : brouillons d’auteur relus et compilés, modèles recoupés, imports publics et contrôle global réussis. Vérification humaine en attente.

### Transport exact des positions et liens des rôles intérieurs

`th.equipped-interior-role-transport` · T2 · refereed

Les rôles intérieurs d’une présentation déployée et de sa reconstruction ont deux applications et deux retours. La position réindexée et le lien complet sont conservés par leurs transports respectifs.

**Hypothèses.** Histoire positive, jonction reçue et transport de signature ; reconstruction sur mêmes State et Step.

**Preuve consommée.** Exact transport des positions de l’épine composé avec le cast de transport_deploy ; positionTransport des rôles et mapSpine_link pour le paquet complet.

**Portée.** Rôle indexé par la même position structurelle, même si des nœuds ou liens bruts se répètent ; pas de transport vers une formation arbitraire.

**Données reçues.** Histoire positive, choix de jonction et reconstruction conservant State/Step.

**Constitution.** Deux retours de rôles intérieurs, position réindexée et paquet complet transporté.

**Lectures dérivées.** Nœuds/liens lus peuvent se répéter ; leur égalité ne fusionne pas les positions.

**Portée constitutive.** T2 de même histoire et formation reconstruite.

**Reprise de l’analyse.** Confirmer et associer à la comparaison de quantité intérieure ; aucune formation arbitraire cible n'est implicitement comparée.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.PositiveHistory.interiorRoleTransport` — [RelationalPerimeter/Constitution/CircularRoleTransport.lean:64](../RelationalPerimeter/Constitution/CircularRoleTransport.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.interior_position_preserved` — [RelationalPerimeter/Constitution/CircularRoleTransport.lean:73](../RelationalPerimeter/Constitution/CircularRoleTransport.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.interior_link_preserved` — [RelationalPerimeter/Constitution/CircularRoleTransport.lean:82](../RelationalPerimeter/Constitution/CircularRoleTransport.lean).

**Relecture.** Referee IA indépendant : sources du lot 4 établies dans leur portée ; 49 sondes sans axiomes, grammaire relative et raccords vérifiés. Coordinateur : brouillons relus/intégrés, modèles compilés, imports publics et vérification globale réussis. Vérification humaine en attente.

### Cinq données choisies du rôle final conservées

`th.equipped-final-role-full-transport` · T2 · refereed

La branche finale se transporte exactement entre la chaîne et sa reconstruction. Jonction, source, cible, différence et provenance choisies ont leurs accords explicites.

**Hypothèses.** circularBoundaryTransport de la même histoire positive et jonction reçue ; rôle final sur sa frontière équipée.

**Preuve consommée.** EquippedFinalRole.exactTransport consomme BoundaryTransport ; retours existants et cinq accords de données choisies.

**Portée.** Unicité par choix conservée, sans unicité de toutes les jonctions ni rigidité des réalisations.

**Données reçues.** CircularBoundaryTransport de la même histoire et jonction choisie.

**Constitution.** Rôle final exact avec cinq accords : jonction, source, cible, différence et provenance.

**Lectures dérivées.** Unicité relative au choix reste ; pas unicité de toutes les jonctions ni rigidité universelle.

**Portée constitutive.** T2 des données sélectionnées sous reconstruction.

**Reprise de l’analyse.** Confirmer et distinguer préservation des choix de leur génération ou de leur unicité globale.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.PositiveHistory.finalRoleTransport` — [RelationalPerimeter/Constitution/CircularRoleTransport.lean:134](../RelationalPerimeter/Constitution/CircularRoleTransport.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.final_witness_preserved` — [RelationalPerimeter/Constitution/CircularRoleTransport.lean:141](../RelationalPerimeter/Constitution/CircularRoleTransport.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.final_source_preserved` — [RelationalPerimeter/Constitution/CircularRoleTransport.lean:148](../RelationalPerimeter/Constitution/CircularRoleTransport.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.final_target_preserved` — [RelationalPerimeter/Constitution/CircularRoleTransport.lean:156](../RelationalPerimeter/Constitution/CircularRoleTransport.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.final_difference_preserved` — [RelationalPerimeter/Constitution/CircularRoleTransport.lean:164](../RelationalPerimeter/Constitution/CircularRoleTransport.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.final_provenance_preserved` — [RelationalPerimeter/Constitution/CircularRoleTransport.lean:171](../RelationalPerimeter/Constitution/CircularRoleTransport.lean).

**Relecture.** Referee IA indépendant : sources du lot 4 établies dans leur portée ; 49 sondes sans axiomes, grammaire relative et raccords vérifiés. Coordinateur : brouillons relus/intégrés, modèles compilés, imports publics et vérification globale réussis. Vérification humaine en attente.

### Branches et classification conservées par transport

`th.equipped-role-classification-commutes` · T2 · refereed

Le transport exact des rôles circulaires conserve leurs branches. Classifier après transport donne Sum.map du transport des positions et de l’identité finale ; generatedPosition commute par Option.map.

**Hypothèses.** Même histoire et sa formation reconstruite ; transports intérieurs et finals équipés déjà construits.

**Preuve consommée.** Assemblage des deux exact transports par constructeurs ; retours des deux branches ; deux commutations point par point.

**Portée.** La branche finale reste sans position engendrée ; pôles et obstruction non transportés ici.

**Données reçues.** Transports exacts des deux branches sur histoire et reconstruction mêmes State/Step.

**Constitution.** Deux retours du rôle complet et commutations classify/Sum.map, generatedPosition/Option.map.

**Lectures dérivées.** La branche finale reste sans position engendrée ; pôles/obstruction non transportés.

**Portée constitutive.** T2 de cette grammaire et reconstruction.

**Reprise de l’analyse.** Confirmer ; utiliser ces carrés dans l'assemblage de quantité circulaire intérieure.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.PositiveHistory.circularRoleTransport` — [RelationalPerimeter/Constitution/CircularRoleTransport.lean:179](../RelationalPerimeter/Constitution/CircularRoleTransport.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.circular_interior_preserved` — [RelationalPerimeter/Constitution/CircularRoleTransport.lean:209](../RelationalPerimeter/Constitution/CircularRoleTransport.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.circular_final_preserved` — [RelationalPerimeter/Constitution/CircularRoleTransport.lean:216](../RelationalPerimeter/Constitution/CircularRoleTransport.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.circular_classification_commutes` — [RelationalPerimeter/Constitution/CircularRoleTransport.lean:239](../RelationalPerimeter/Constitution/CircularRoleTransport.lean).
- `RelationalPerimeter.Constitution.PositiveHistory.circular_generated_position_commutes` — [RelationalPerimeter/Constitution/CircularRoleTransport.lean:248](../RelationalPerimeter/Constitution/CircularRoleTransport.lean).

**Relecture.** Referee IA indépendant : sources du lot 4 établies dans leur portée ; 49 sondes sans axiomes, grammaire relative et raccords vérifiés. Coordinateur : brouillons relus/intégrés, modèles compilés, imports publics et vérification globale réussis. Vérification humaine en attente.

### Unicité résiduelle du noyau

`th.residual` · T2 · refereed

Toute occurrence nouvelle porte le centre résiduel ; deux nouvelles occurrences coïncident. Une partie nouvelle positive fournit une occurrence distinguée unique.

**Hypothèses.** Rôle résiduel contractile, exclusion des étiquettes internes et injectivité du nouvel étiquetage ; positivité pour fournir un habitant.

**Preuve consommée.** label_is_residual utilise l’exclusion et la contraction ; occurrences_unique utilise ensuite newLabelInjective.

**Données reçues.** Rôle contractile, exclusion intérieure, injectivité ; habitant supplémentaire pour le centre nouveau.

**Constitution.** Étiquette résiduelle puis sous-singleton ; positivité donne un témoin unique.

**Lectures dérivées.** Le label lit une occurrence ; il ne la crée pas. label_is_residual n'utilise pas l'injectivité.

**Portée constitutive.** T2 abstrait conditionnel au noyau ; pas clôture ou génération universelle.

**Reprise de l’analyse.** Confirmer le T2 et séparer le label, l'unicité et l'habitation ; ne pas lire ce noyau comme origine de l'intérieur.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `SegmentedResidualRole.ResidualDeterminationCore.occurrences_unique` — [SegmentedResidualRole.lean:136](../SegmentedResidualRole.lean).
- `SegmentedResidualRole.positiveCore_hasUniqueResidualOccurrence` — [SegmentedResidualRole.lean:167](../SegmentedResidualRole.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Reconstruction interne sous conditions supplémentaires

`th.internal-reconstruction` · T2 · refereed

Un noyau résiduel positif reconstruit ExactInternalCompletion si embedOld est injectif ; la positivité permet de retrouver des étiquettes anciennes internes.

**Hypothèses.** ResidualUniquenessKernel, PositiveNewPart, Function.Injective kernel.embedOld.

**Preuve consommée.** oldLabelsInternal_of_positive puis ExactReconstructionConditions.toExactInternalCompletion.

**Données reçues.** ResidualUniquenessKernel, nouvelle partie positive, injectivité de embedOld.

**Constitution.** Internalité des labels anciens, inverse occurrenceToRole et deux retours.

**Lectures dérivées.** L'inverse du même placement est unique point par point ; toutes les réalisations possibles ne sont pas identifiées.

**Portée constitutive.** T2 de reconstruction relative à un noyau fixé.

**Reprise de l’analyse.** Confirmer et préserver l'injectivité ancienne ; présenter cette reconstruction comme acquis positif sur l'intérieur.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `SegmentedResidualRole.ResidualUniquenessKernel.toExactInternalCompletion_of_positive` — [SegmentedResidualRole.lean:595](../SegmentedResidualRole.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Classification et sortie du régime abstrait

`th.abstract-exit` · T2 · refereed

Un régime dont chaque candidat est canonique ou produit une tentative rejetée classe exactement la frontière ; la continuation stricte n’est pas admise.

**Hypothèses.** BoundaryGenerator avec extension irréflexive ; canonicalRegime, classifyOrTotalize, rejectTotalization.

**Preuve consommée.** Classification par analyse des deux branches ; sortie par continuation_ne_boundary.

**Portée.** Résultat conditionnel sur une règle de régime explicite ; ce n’est pas une conséquence de la seule circularité.

**Données reçues.** Générateur avec extension irréflexive ; frontière admise ; analyse canonique-ou-tentative ; rejet.

**Constitution.** Classification exacte du régime puis continuation hors régime.

**Lectures dérivées.** Le diagnostic conserve le candidat ; sa non-admission n'annule pas sa constitution.

**Portée constitutive.** T2 conditionnel au régime explicite, indépendant d'une circularité universelle.

**Reprise de l’analyse.** Confirmer ; citer précisément classifyOrTotalize et rejectTotalization comme hypothèses de sortie.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `AbstractSegmentedTurning.ObstructedRegime.exactClassification` — [AbstractSegmentedTurning.lean:352](../AbstractSegmentedTurning.lean).
- `AbstractSegmentedTurning.ObstructedRegime.continuation_outside_regime` — [AbstractSegmentedTurning.lean:370](../AbstractSegmentedTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Continuation positivement engendrée et stricte

`th.positive-continuation` · T2 · refereed

oneStepAfterPerimeter construit un pas après le périmètre et une extension stricte, distincte du déploiement canonique.

**Hypothèses.** CircularPresentation P et le générateur libre courant.

**Preuve consommée.** Génération effective, histoire singleton positive et irréflexivité du préfixe strict.

**Données reçues.** Présentation historique et générateur canonique disponible au terme.

**Constitution.** Un pas effectif, histoire à un pas, extension stricte distincte du déploiement.

**Lectures dérivées.** La continuation est extérieure à ce périmètre, pas à toute constitution possible.

**Portée constitutive.** T2 de l'instance historique ; continuation effectivement choisie.

**Reprise de l’analyse.** Confirmer et distinguer intérieur complet, prolongement constitué et admission du prolongement.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

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

**Données reçues.** History.Positive sur GeneratedStep et PositiveConstitution canoniques.

**Constitution.** Avancée stricte des curseurs et inégalité des états source/cible.

**Lectures dérivées.** Des valeurs nodales brutes peuvent se répéter malgré la distinction des constitutions.

**Portée constitutive.** T2 de génération libre canonique ; pas non-cyclicité de tout Step.

**Reprise de l’analyse.** Confirmer ; ne pas exporter la loi au PositiveHistory générique ni la confondre avec séparation des pôles.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `StrongPerimetralTurning.positiveGeneratedHistory_source_ne_target` — [StrongPerimetralTurning.lean:2556](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Toute continuation positive fidèlement classée a un résidu unique

`th.labelled-residual` · T2 · refereed

Dans une FaithfullyLabelledPerimeterExtension positive, toute nouvelle occurrence porte FinalRequirement et les occurrences de la continuation sont uniques.

**Hypothèses.** Extension périmétrale, étiquetage fidèle préservant les anciennes positions et continuation positive.

**Preuve consommée.** Passage vers SegmentedResidualRole et contractibilité de FinalRequirement.

**Portée.** Le noyau canonique oneStepResidualDeterminationCore définit séparément un label final constant et utilise ExactlyOne pour son injectivité ; ne pas confondre les deux chemins de preuve.

**Données reçues.** Extension recomposable, label injectif préservant les anciennes positions, résidu contractile ; positivité pour habiter.

**Constitution.** Exclusion intérieure, label final et unicité de la partie nouvelle via segmentation.

**Lectures dérivées.** La détermination du label n'est pas un nouveau témoin arbitraire RealizesFull ; le chemin canonique à un pas a une autre source d'unicité.

**Portée constitutive.** T2 dans les extensions fidèlement classées du même système de rôles.

**Reprise de l’analyse.** Confirmer ; garder séparés preuve générale de segmentation et noyau direct utilisant ExactlyOne.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

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

**Données reçues.** CircularRefinement : extension, fidélité, accords intérieurs, realizesFinal ; obstruction héritée.

**Constitution.** Équivalence constructive avec le déploiement canonique et non-admission du premier pas supplémentaire.

**Lectures dérivées.** Le même générateur continue ; finalJunction seul ne fournit pas realizesFinal.

**Portée constitutive.** T2 relatif à ce régime obstrué.

**Reprise de l’analyse.** Confirmer et faire apparaître realizesFinal comme obligation indépendante qui produit la tentative bilatérale.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `StrongPerimetralTurning.exactCircularRefinementClassification` — [StrongPerimetralTurning.lean:6853](../StrongPerimetralTurning.lean).
- `StrongPerimetralTurning.oneStepAfterPerimeter_notCircularRefinement` — [StrongPerimetralTurning.lean:6864](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Admission et satisfaction : adéquation démontrée

`th.specification` · T2 · refereed

CircularRefinement fournit CircularSpecificationSatisfaction ; réciproquement la satisfaction fournit le raffinement, avec des témoins et interfaces distincts.

**Hypothèses.** Spécification avec exactitude locale et clause trajectorielle ; obstruction au TotalLoop.

**Preuve consommée.** Factorisation locale, classification du périmètre et rejet de la tentative produite par une extension stricte.

**Données reçues.** Spécification locale avec clause trajectorielle ; régime de raffinement et obstruction au TotalLoop.

**Constitution.** Passages soundness et complétude entre témoins de satisfaction et raffinement.

**Lectures dérivées.** La même classification d'histoires n'identifie pas les structures de régime et de spécification.

**Portée constitutive.** T2 sur les signatures historiques explicites.

**Reprise de l’analyse.** Confirmer ; la sortie de spécification repose sur sa clause trajectorielle, pas sur seule circularité positive.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `StrongPerimetralTurning.circularRefinement_soundSpecification` — [StrongPerimetralTurning.lean:6906](../StrongPerimetralTurning.lean).
- `StrongPerimetralTurning.circularSpecification_complete` — [StrongPerimetralTurning.lean:6086](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Certificat du tournant périmétral affirmatif

`th.turning` · T2 · refereed

strongPerimetralTurning rassemble génération positive, réalisation exacte, absorption des parties admissibles, refus des totalisations et continuation au-delà du périmètre.

**Hypothèses.** CircularPresentation avec ses données et son obstruction initiale.

**Preuve consommée.** Assemblage de résultats déjà construits ; voir les champs et leurs producteurs, sans déduire une dépendance causale de leur seule présence.

**Données reçues.** Présentation avec architecture positive, pôles et obstruction.

**Constitution.** Génération, déploiement exact, absorption des parties, interprétations et rejets via producteurs existants.

**Lectures dérivées.** L'assemblage ne prouve pas à lui seul nécessité causale de chaque champ ; les accords de la chaîne doivent être suivis.

**Portée constitutive.** T2 sur CircularPresentation obstruée ; pas théorème universel de toute relation.

**Reprise de l’analyse.** Confirmer et raconter d'abord le domaine intérieur puis le prolongement et son statut conditionnel.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `StrongPerimetralTurning.strongPerimetralTurning` — [StrongPerimetralTurning.lean:7001](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Interprétation exacte des occurrences concrètes

`th.concrete-interpretation` · T2 · refereed

Toute ConcreteContinuationAlgebra fournit une ExactHistoryInterpretation de chaque histoire libre, avec deux retours des occurrences.

**Hypothèses.** ConcreteContinuationAlgebra avec son interface de pas concrets et ses accords primitifs ; les applications et retours des occurrences sont reconstruits par induction.

**Preuve consommée.** realizeHistory, applications entre occurrences, lois concreteBackwardForward et concreteForwardBackward.

**Portée.** Ne fournit pas l’injectivité de toutes les lectures d’états ou de valeurs ; la fidélité des cibles exige une hypothèse propre.

**Données reçues.** Algèbre de continuation concrète, lectures et accords primitifs des pas.

**Constitution.** Histoire concrète et deux retours d'occurrences par induction.

**Lectures dérivées.** Les lectures d'états/interfaces ne sont pas toutes injectives ; exactitude d'occurrences ne vaut pas équivalence entière des données.

**Portée constitutive.** T2 conditionnel à ConcreteContinuationAlgebra ; pas validation computationnelle.

**Reprise de l’analyse.** Confirmer ; situer les lectures appauvries et réserver la fidélité des cibles à une hypothèse propre.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `StrongPerimetralTurning.exactlyInterpretHistory` — [StrongPerimetralTurning.lean:7607](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Séparateur existant : exactitude locale sans ordre

`th.separator-order` · T2 · refereed

La réalisation sémantique permutée de l’exemple à quatre nœuds est localement exacte et injective, mais ne conserve pas la précédence.

**Hypothèses.** SemanticTrace affaiblie et examplePresentation ; contre-exemple dans cette présentation.

**Preuve consommée.** Permutation explicite, inversion des deux premières adresses et asymétrie de Nat.lt.

**Données reçues.** SemanticTrace affaiblie de l'exemple et permutation des pas localement exacts.

**Constitution.** Réalisation injective locale avec inversion des deux premières adresses.

**Lectures dérivées.** La liste expérimentale et ses indices oublient l'enracinement/composition ; ce n'est pas l'intérieur fort.

**Portée constitutive.** T2 de contre-modèle précis sur la trace à quatre nœuds.

**Reprise de l’analyse.** Confirmer le séparateur ; il justifie la portée du théorème fort, pas une insuffisance de l'intérieur constitué.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `StrongPerimetralTurning.Example.permutedExample_not_order_preserved` — [StrongPerimetralTurning.lean:8161](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Séparateur existant : ordre sans pont composable

`th.separator-bridge` · T2 · refereed

La trace intercalée de l’exemple conserve la précédence mais n’a pas de pont constitutif effectif entre les première et deuxième positions adjacentes.

**Hypothèses.** SemanticTrace de l’exemple, accord local et occurrences supplémentaires intercalées.

**Preuve consommée.** Positions ordonnées 0, 2, 4 ; occurrence intercalaire et bridgeParticipation_between_empty_of_next.

**Données reçues.** Trace intercalée, accords locaux et ordre des images canoniques.

**Constitution.** Ordre préservé et impossibilité du pont effectif entre exigences adjacentes de l'exemple.

**Lectures dérivées.** Les occurrences intercalaires restent individuellement présentes ; leur ordre n'est pas une composition typée.

**Portée constitutive.** T2 de contre-modèle de trace affaiblie.

**Reprise de l’analyse.** Confirmer ; placer en regard de la reconstruction positive de succession immédiate dans RootedGeneratedHistory.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `StrongPerimetralTurning.Example.interleavedExample_order_preserved` — [StrongPerimetralTurning.lean:8284](../StrongPerimetralTurning.lean).
- `StrongPerimetralTurning.Example.interleavedExample_no_effective_bridge_p1_p2` — [StrongPerimetralTurning.lean:8356](../StrongPerimetralTurning.lean).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Nouveau contre-modèle : retirer la fidélité détruit l’unicité

`th.separator-injectivity` · T2 · refereed

Deux nouvelles occurrences Bool ont le même label dans un résidu Unit contractile, sans aucun label interne Empty, et restent distinctes.

**Hypothèses.** Core affaibli : injectivité du nouvel étiquetage supprimée ; anciennes occurrences absentes.

**Preuve consommée.** Étiquette constante sur Bool ; false ≠ true.

**Données reçues.** Porteur nouveau Bool, résidu Unit, intérieur Empty, label constant.

**Constitution.** Deux occurrences distinctes partageant le même label, non-injectivité.

**Lectures dérivées.** L'égalité de lecture de rôle ne devient pas égalité d'occurrences.

**Portée constitutive.** T2 de modèle du noyau affaibli sans injectivité.

**Reprise de l’analyse.** Confirmer ; la nécessité testée concerne l'injectivité dans cette inférence, pas toute axiomatisation possible.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `FoundationalSeparators.weakened_core_does_not_force_uniqueness` — [labyrinth/probes/FoundationalSeparators.lean.in:33](../labyrinth/probes/FoundationalSeparators.lean.in).
- `FoundationalSeparators.residual_label_not_injective` — [labyrinth/probes/FoundationalSeparators.lean.in:27](../labyrinth/probes/FoundationalSeparators.lean.in).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Nouveau contre-modèle : transport exact sans conservation de l’ordre

`th.separator-transport` · T2 · refereed

L’involution Bool.not est un ExactTypeTransport Bool Bool qui inverse une relation Before false true et ne la préserve pas.

**Hypothèses.** Deux lois de retour ; aucune obligation de conservation de Before dans ExactTypeTransport.

**Preuve consommée.** Bool.not et élimination de Before true false.

**Données reçues.** Transport Bool.not avec retours ; relation Before false true.

**Constitution.** Réfutation de la conservation de Before pour ces applications.

**Lectures dérivées.** Les retours du porteur ne contiennent aucune loi d'ordre.

**Portée constitutive.** T2 de contre-modèle à une inférence sur transport nu.

**Reprise de l’analyse.** Confirmer ; ne pas appeler cette correspondance un transport constitutif riche.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `FoundationalSeparators.swap_does_not_preserve_order` — [labyrinth/probes/FoundationalSeparators.lean.in:80](../labyrinth/probes/FoundationalSeparators.lean.in).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Diagnostic : le rôle final nu est uniformément ponctuel

`th.final-role-carrier` · T2 · refereed

Pour toute présentation P, FinalRequirement P possède un transport exact explicite vers Unit.

**Hypothèses.** Uniquement le type inductif FinalRequirement P à un constructeur.

**Preuve consommée.** Élimination du rôle et de Unit ; aucune jonction ni occurrence n’est transportée.

**Portée.** Diagnostic du porteur contractile à présentation fixée. Son index P demeure ; les données de frontière et leurs transports doivent être étudiés par leurs propres interfaces. Ce diagnostic ne réfute pas la priorité relationnelle.

**Données reçues.** Type historique FinalRequirement à un constructeur et parent P comme paramètre.

**Constitution.** Transport uniforme exact vers Unit.

**Lectures dérivées.** Le porteur nu ne transporte ni jonction, ni occurrence, ni lois de frontière ; l'index peut rester un paramètre de l'équivalence.

**Portée constitutive.** T2 de porteur nu ; aucune réfutation de la famille équipée.

**Reprise de l’analyse.** Confirmer ; préciser que l'oubli des données et lois, non la seule existence d'Unit, limite cette lecture.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `FoundationalSeparators.finalRoleUnitTransport` — [labyrinth/probes/FoundationalSeparators.lean.in:86](../labyrinth/probes/FoundationalSeparators.lean.in).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Nouveau contre-modèle : positivité sans reconstruction intérieure

`th.separator-old-completion` · T2 · refereed

Un ResidualUniquenessKernel peut avoir une partie nouvelle positive et un résidu unique sans admettre aucune ExactInternalCompletion : les anciennes occurrences peuvent être fusionnées par embedOld.

**Hypothèses.** Ancien porteur Bool, rôle interne Unit et partie nouvelle Unit ; plongement ancien constant. Deux constructions distinctes, avec porteurs étendus Bool et Option Unit.

**Preuve consommée.** Le retour occurrenceRoundTrip de la complétion demandée forcerait false = true ou true = false. Le noyau segmenté conserve pourtant un étiquetage étendu fidèle et la positivité nouvelle.

**Portée.** Réfute la suppression de l’injectivité ancienne dans la reconstruction ; ne met pas en cause l’unicité résiduelle.

**Données reçues.** Noyau à anciens Bool fusionnés, nouvelle partie Unit positive et label étendu fidèle.

**Constitution.** Unicité nouvelle mais impossibilité d'ExactInternalCompletion.

**Lectures dérivées.** Label du porteur étendu ne restaure pas des anciennes occurrences déjà fusionnées par embedOld.

**Portée constitutive.** T2 de contre-modèles précis ; reconstruction positive garde embedOldInjective.

**Reprise de l’analyse.** Confirmer ; le séparateur ne réfute ni unicité résiduelle ni déploiement intérieur canonique.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `FoundationReferee.collapsedOld_no_exact_completion` — [research/agents/referee-foundations/IndependentProbes.lean.in:35](../research/agents/referee-foundations/IndependentProbes.lean.in).
- `FoundationalSeparators.positive_kernel_does_not_force_internal_completion` — [labyrinth/probes/FoundationalSeparators.lean.in:65](../labyrinth/probes/FoundationalSeparators.lean.in).

**Relecture.** Énoncé et hypothèses relus contre les sources par un referee IA indépendant ; corrections appliquées et sondes recoupées par le coordinateur. Vérification humaine en attente.

### Une bijection de fibre peut perdre la jonction choisie

`th.separator-closing-witness` · T2 · refereed

Un transport exact de tous les porteurs conserve les trois indices mais échange les témoins Bool de clôture ; ce transport spécifié ne peut s’enrichir en BoundaryTransport.

**Hypothèses.** Même frontière pointée ; Bool.not seulement sur la fibre de clôture, identité ailleurs.

**Preuve consommée.** false est envoyé sur true ; junctionExact imposerait true = false.

**Portée.** Ne réfute pas tous les transports riches entre ces frontières : l’identité existe.

**Données reçues.** Même frontière, Bool.not sur la fibre fermante et identités ailleurs.

**Constitution.** Trois indices préservés, jonction changée, impossibilité de relever ces cartes en BoundaryTransport.

**Lectures dérivées.** Le choix est une donnée distincte de l'exactitude du porteur de témoins.

**Portée constitutive.** T2 de contre-modèle à applications fixées ; identité riche existe.

**Reprise de l’analyse.** Confirmer sans généraliser à l'absence de tout transport riche entre ces frontières.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

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

**Données reçues.** Modèle indépendant Bool, échange de provenance seulement.

**Constitution.** Indices/jonction préservés et impossibilité d'enrichir ces mêmes cartes avec provenanceExact.

**Lectures dérivées.** Une conservation de compatibilité ne reconstitue pas celle de provenance.

**Portée constitutive.** T2 de contre-modèle d'accord manquant.

**Reprise de l’analyse.** Confirmer la loi séparée, sans exiger la génération de la provenance reçue.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

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

**Données reçues.** Chaîne positive à un pas sur un même LocalNode et témoin fermant.

**Constitution.** Égalité du nœud terminal/initial ; position positive distincte de cette lecture.

**Lectures dérivées.** Retour de nœud brut ne signifie pas retour des curseurs historiques ou occurrence périodique.

**Portée constitutive.** T2 de données positives ; pas périodicité générée.

**Reprise de l’analyse.** Confirmer et rattacher à l'individuation par place/histoire, centrale à la priorité relationnelle.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.Examples.raw_node_return` — [RelationalPerimeter/Constitution/Examples.lean:72](../RelationalPerimeter/Constitution/Examples.lean).
- `PositiveFoundationReferee.repeatedRawNode` — [research/agents/referee-positive-foundations/IndependentProbes.lean.in:47](../research/agents/referee-positive-foundations/IndependentProbes.lean.in).

**Relecture.** Énoncé et portée relus par un referee IA indépendant ; sondes propres sur cinq porteurs et deux échanges distincts. Build complet et contrôle constructif par le coordinateur. Vérification humaine en attente.

### Génération positive sans clôture disponible

`th.separator-generated-unclosed` · T2 · refereed

Un pas admissible false→true déploie une chaîne positive, tandis que sa fibre fermante true→false est Empty. Aucun pointage ne ferme cette chaîne générée.

**Hypothèses.** Compatibilité dirigée, DirectedStep.forward, histoire d’un pas et indices du déploiement.

**Preuve consommée.** directedPositive donne here ; la fibre fermante calcule Empty ; noPointingOfEmpty interdit le pointage.

**Portée.** Contre-modèle à une clôture automatiquement déduite de positivité, sans réfuter les présentations recevant une jonction distincte.

**Données reçues.** Pas dirigé false→true et famille Compatible correspondante.

**Constitution.** Déploiement positif dont ClosingWitness true→false est Empty ; aucun pointage.

**Lectures dérivées.** La forme lit des extrêmes réellement construits ; absence de témoin final ne supprime pas l'histoire.

**Portée constitutive.** T2 de modèle dirigé.

**Reprise de l’analyse.** Confirmer ; réfute clôture automatique seulement, pas présentations munies d'une jonction reçue.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

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

**Données reçues.** Deux pas true/false sur Unit, même nœud brut.

**Constitution.** Occurrences et positions distinctes ; compatibilités distinctes malgré même nœud.

**Lectures dérivées.** Le retour d'état est permis dans PositiveHistory ; les positions conservent la participation à la chaîne.

**Portée constitutive.** T2 de modèle de formation générique.

**Reprise de l’analyse.** Confirmer et donner forte visibilité ; ce séparateur soutient directement l'orientation relationnelle.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.PositiveGenerationExamples.raw_nodes_repeat` — [RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:159](../RelationalPerimeter/Constitution/PositiveGenerationExamples.lean).
- `RelationalPerimeter.Constitution.PositiveGenerationExamples.repeated_occurrences_distinct` — [RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:163](../RelationalPerimeter/Constitution/PositiveGenerationExamples.lean).
- `RelationalPerimeter.Constitution.PositiveGenerationExamples.repeated_positions_distinct` — [RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:166](../RelationalPerimeter/Constitution/PositiveGenerationExamples.lean).
- `RelationalPerimeter.Constitution.PositiveGenerationExamples.repeated_step_witnesses_distinct` — [RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:172](../RelationalPerimeter/Constitution/PositiveGenerationExamples.lean).

**Relecture.** Referee IA indépendant : lot 2 établi dans la signature de chemins/déploiement ; 38 sondes sans axiomes, données différentes et réindexation vérifiée. Coordinateur : modèles recoupés, build et script global réussis. Vérification humaine en attente.

### Mêmes sortes sans transport possible des fibres

`th.separator-sort-fibres` · T2 · refereed

Deux signatures ont les mêmes sortes Bool mais des fibres de compatibilité Unit et Empty. Aucun transport complet, même existant propositionnellement, ne relie ces signatures.

**Hypothèses.** inhabitedSignature et emptySignature ; Unit fourni dans une fibre source.

**Preuve consommée.** La carte forward du transport de cette fibre produirait un terme Empty ; élimination.

**Portée.** Une bijection des sortes ne suffit pas à transporter les relations primitives.

**Données reçues.** Sortes Bool communes, fibres Compatible Unit et Empty.

**Constitution.** Impossibilité de tout transport complet de ces familles.

**Lectures dérivées.** Oublier les familles laisse des sorts identiques tout en perdant l'habitation de relations.

**Portée constitutive.** T2 de modèle précis sur signatures.

**Reprise de l’analyse.** Confirmer ; ce modèle soutient l'antériorité des relations pertinentes aux comparaisons, sans prétendre engendrer les supports.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.SignatureTransportExamples.same_explicit_sorts` — [RelationalPerimeter/Constitution/SignatureTransportExamples.lean:27](../RelationalPerimeter/Constitution/SignatureTransportExamples.lean).
- `RelationalPerimeter.Constitution.SignatureTransportExamples.no_family_transport_nonempty` — [RelationalPerimeter/Constitution/SignatureTransportExamples.lean:37](../RelationalPerimeter/Constitution/SignatureTransportExamples.lean).

**Relecture.** Referee IA indépendant : sources du lot 3 établies dans leur portée ; 62 sondes sans axiomes, fibres variables et closing Empty vérifiées. Coordinateur : brouillons d’auteur relus et compilés, modèles recoupés, imports publics et contrôle global réussis. Vérification humaine en attente.

### Choix de jonction et extension de la grammaire restent possibles

`th.separator-relative-role-grammar` · T2 · refereed

Une frontière vide avant choix n’a aucun rôle final sur un pointage. Deux choix Bool sur une même forme ont des témoins de rôles distincts. Un rôle extérieur dans CircularRole ⊕ Unit n’est pas couvert par la grammaire initiale, dont l’exhaustivité relative reste vraie.

**Hypothèses.** Forme vide directe, deux présentations de même forme à jonctions false/true, type de rôles explicitement élargi.

**Preuve consommée.** NoFinalRoleOfEmpty ; distinction des témoins Bool ; séparation des constructeurs de Sum pour le rôle extérieur.

**Portée.** Contre-modèle à une exhaustivité universelle déduite de la classification déclarée, pas une réfutation de son exhaustivité relative.

**Données reçues.** Forme vide, deux choix Bool, extension explicite CircularRole ⊕ Unit.

**Constitution.** Impossibilité finale sur fibre vide, témoins de choix distincts, extérieur hors image.

**Lectures dérivées.** Ajouter une branche change le domaine ; cela ne réfute pas l'exhaustivité du système intérieur/final initial.

**Portée constitutive.** T2 de modèles précis ; borne d'annonce relative.

**Reprise de l’analyse.** Confirmer et présenter comme test de frontière d'annonce, pas critique de la nécessité relationnelle de l'intérieur.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

**Déclarations.**

- `RelationalPerimeter.Constitution.CircularRolesExamples.unpointed_empty_no_final` — [RelationalPerimeter/Constitution/CircularRolesExamples.lean:32](../RelationalPerimeter/Constitution/CircularRolesExamples.lean).
- `RelationalPerimeter.Constitution.CircularRolesExamples.chosen_witnesses_distinct` — [RelationalPerimeter/Constitution/CircularRolesExamples.lean:22](../RelationalPerimeter/Constitution/CircularRolesExamples.lean).
- `RelationalPerimeter.Constitution.CircularRolesExamples.no_exhaustiveness_of_larger_type` — [RelationalPerimeter/Constitution/CircularRolesExamples.lean:64](../RelationalPerimeter/Constitution/CircularRolesExamples.lean).

**Relecture.** Referee IA indépendant : sources du lot 4 établies dans leur portée ; 49 sondes sans axiomes, grammaire relative et raccords vérifiés. Coordinateur : brouillons relus/intégrés, modèles compilés, imports publics et vérification globale réussis. Vérification humaine en attente.

## Voies réfutées et leçons

### L’exactitude locale imposerait l’ordre sur toute trace

Réfuté sur SemanticTrace par l’exemple permuté.

**Leçon.** L’ordre reconstruit requiert la composition et l’enracinement du carrier fort.

**Données reçues.** Modèle permuté de SemanticTrace.

**Constitution.** Réfutation du transfert de l'ordre depuis la seule exactitude locale.

**Lectures dérivées.** Le carrier fort garde les données qui permettent de reconstruire l'ordre.

**Portée constitutive.** Voie réfutée dans la signature affaiblie, pas sur toute histoire relationnelle.

**Reprise de l’analyse.** Conserver et rattacher au séparateur-order et au résultat positif rooted-structure.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### L’ordre suffirait à la participation composable

Réfuté sur SemanticTrace par l’exemple intercalé.

**Leçon.** Conserver la précédence ne fournit pas un pont constitutif effectif entre positions adjacentes.

**Données reçues.** Modèle intercalé ordonné.

**Constitution.** Réfutation ordre seul implique participation composable.

**Lectures dérivées.** Un intervalle ordonné ne fournit pas son histoire-pont et sa couverture exacte.

**Portée constitutive.** Voie réfutée sur SemanticTrace.

**Reprise de l’analyse.** Conserver en indiquant l'oubli de composition, sans affaiblir le résultat intérieur canonique.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Contractibilité et exclusion suffiraient à l’unicité

Réfuté par deux occurrences Bool portant le même label final.

**Leçon.** Garder l’injectivité du nouvel étiquetage ; ce contre-modèle teste sa suppression, sans prouver une minimalité de toutes les hypothèses.

**Données reçues.** Label constant sur deux Bool, résidu contractile et exclusion intérieure.

**Constitution.** Réfutation de l'unicité sans injectivité.

**Lectures dérivées.** Le résidu lu ne fusionne pas les occurrences constituées.

**Portée constitutive.** Voie réfutée pour noyau privé de newLabelInjective.

**Reprise de l’analyse.** Conserver avec une leçon limitée à cette suppression, pas une minimalité globale.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Le transport exact entre types conserverait toute relation

Réfuté par le transport Bool.not sur Before.

**Leçon.** Ajouter des accords relationnels explicites aux deux lois de retour.

**Données reçues.** Bool.not et Before.

**Constitution.** Réfutation de conservation automatique de toute relation par ExactTypeTransport.

**Lectures dérivées.** Transport nu oublie la relation choisie.

**Portée constitutive.** Voie réfutée sur une signature neutre.

**Reprise de l’analyse.** Conserver et mettre les transports riches déjà construits en regard.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### La positivité du noyau suffirait à reconstruire l’intérieur exact

Réfuté par deux anciens Bool fusionnés dans un noyau pourtant positif et fidèlement étiqueté sur son porteur étendu.

**Leçon.** Pour reconstruire la réalisation intérieure, conserver l’injectivité de embedOld ; la positivité permet seulement de retrouver les étiquettes anciennes internes.

**Données reçues.** Noyau positif avec embedOld non injectif.

**Constitution.** Réfutation reconstruction exacte depuis positivité seule.

**Lectures dérivées.** Les anciennes occurrences fusionnées ne sont plus décodables.

**Portée constitutive.** Voie réfutée du noyau faible.

**Reprise de l’analyse.** Conserver la leçon et l'acquis positif de reconstruction sous injectivité ancienne.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### La bijection exacte conserverait le témoin choisi

Réfuté par Bool.not sur la fibre de compatibilité fermante, avec trois indices inchangés.

**Leçon.** Exiger junctionExact en plus des lois de retour.

**Données reçues.** Échange Bool.not de jonction sur indices fixes.

**Constitution.** Réfutation de bijection implique conservation du témoin choisi.

**Lectures dérivées.** La loi junctionExact est absente du porteur nu.

**Portée constitutive.** Voie réfutée sur cartes faibles fixées.

**Reprise de l’analyse.** Conserver ; montrer les morphismes riches existants comme réponse positive.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Conserver la jonction suffirait à conserver la provenance

Réfuté par un échange de provenance indépendant, sans changement des indices ni de la jonction.

**Leçon.** Exiger provenanceExact séparément.

**Données reçues.** Jonction conservée et provenance Bool échangée.

**Constitution.** Réfutation d'une conservation automatique de provenance.

**Lectures dérivées.** Deux données de témoins restent distinctes.

**Portée constitutive.** Voie réfutée sur une signature sélectionnée.

**Reprise de l’analyse.** Conserver provenanceExact séparément ; ne pas en déduire insuffisance de la constitution intérieure.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### La positivité circulaire interdirait tout retour du nœud brut

Réfuté par une chaîne positive d’un pas sur le même nœud.

**Leçon.** Distinguer nœuds bruts, curseurs et occurrences engendrées.

**Données reçues.** Chaîne positive sur même valeur de nœud.

**Constitution.** Réfutation positivité interdit toute récurrence brute.

**Lectures dérivées.** Même nœud peut occuper plusieurs places constituées.

**Portée constitutive.** Voie réfutée pour nœuds bruts, pas curseurs stricts.

**Reprise de l’analyse.** Conserver et mettre en évidence la différence occurrence/valeur lue.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### L’unicité du rôle par choix imposerait une jonction unique

Réfuté par une même forme Bool avec deux pointages distincts et un rôle unique sur chaque pointage.

**Leçon.** Fixer le choix dans la quantification du théorème de rôle ; ne pas identifier la fibre de rôles sur un choix avec la famille de tous les choix.

**Données reçues.** Même forme Bool avec deux choix.

**Constitution.** Réfutation unicité du rôle par choix implique jonction unique.

**Lectures dérivées.** La projection du rôle au choix change le domaine de quantification.

**Portée constitutive.** Voie réfutée sur modèle Bool.

**Reprise de l’analyse.** Conserver avec leçon centrée sur quantification, pas existence d'un choix arbitraire d'objets.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Une chaîne positive fournirait sa propre jonction

Réfuté par une histoire dirigée positive dont la fibre fermante est Empty.

**Leçon.** Fournir une jonction distincte pour la clôture ; séparer existence de pas et existence de boucle fermante.

**Données reçues.** Modèle dirigé positif à fibre fermante vide.

**Constitution.** Réfutation positivité produit une jonction.

**Lectures dérivées.** L'histoire reste constituée sans pointage final.

**Portée constitutive.** Voie réfutée sur formation générique.

**Reprise de l’analyse.** Conserver et distinguer manque de clôture de manque de domaine intérieur.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### La formation admissible déterminerait un successeur unique

Réfuté par deux pas depuis le même état vers deux cibles différentes, et deux continuations choisies différentes.

**Leçon.** La sélection d’une continuation est une donnée supplémentaire ; les théorèmes canoniques ne sont pas universels.

**Données reçues.** Deux pas et deux choix globaux dans le modèle ramifié.

**Constitution.** Réfutation successeur unique dans toute formation.

**Lectures dérivées.** Une continuation choisie lit une branche disponible sans effacer les autres.

**Portée constitutive.** Voie réfutée sur interface générique.

**Reprise de l’analyse.** Conserver ; tests du tournant futur doivent fixer leur continuation propre.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Deux lectures du même nœud seraient la même occurrence

Réfuté par deux pas sur le même nœud avec here et later here distincts.

**Leçon.** Conserver l’histoire et la position du pas ; la valeur brute ne suffit pas à identifier l’occurrence.

**Données reçues.** Même nœud sur deux pas de repeatedHistory.

**Constitution.** Réfutation de fusion d'occurrences/positions via égalité nodale.

**Lectures dérivées.** Lecture nodale est ultérieure et non injective.

**Portée constitutive.** Voie réfutée soutenant l'individuation relationnelle.

**Reprise de l’analyse.** Conserver et présenter comme un résultat positif pour la priorité relationnelle, pas seule réserve technique.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Les bijections de sortes suffiraient pour toutes les familles

Réfuté par mêmes sortes Bool et fibres de compatibilité Unit/Empty.

**Leçon.** Fournir les transports exacts de chaque fibre aux indices transportés ; ne pas déduire leur habitation des seules sortes.

**Données reçues.** Unit/Empty sur mêmes sortes Bool.

**Constitution.** Réfutation bijections de sortes suffisent pour transport de fibres.

**Lectures dérivées.** La signature relationnelle est une donnée propre.

**Portée constitutive.** Voie réfutée de transport faible.

**Reprise de l’analyse.** Conserver avec transports complets comme résultat positif répondant à cette insuffisance.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Une grammaire exhaustive couvrirait tout rôle extérieur possible

Réfuté : CircularRole P est classifié exactement, tandis que son extension CircularRole P ⊕ Unit possède un élément extérieur à l’image de cette grammaire.

**Leçon.** Annoncer l’exhaustivité relative au type déclaré. L’ajout explicite d’une branche change le domaine de classification ; il ne réfute pas l’exactitude de l’intérieur constitué. Étendre la grammaire exige une nouvelle classification.

**Données reçues.** Ajout explicite d'un Unit extérieur à CircularRole.

**Constitution.** Réfutation d'une exhaustivité sur cette extension.

**Lectures dérivées.** Le système initial reste exactement classifié ; le texte conceptuel annonçait déjà relativité à la présentation.

**Portée constitutive.** Voie réfutée pour inférence universelle, pas pour l'exhaustivité intérieure visée.

**Reprise de l’analyse.** Conserver en précisant que changer le type de rôles change la portée ; ne pas imputer cette inférence au projet comme primitive.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

## Portes de recherche

### Circularité positive autonome

`q.positive-circle` · answered

La séparation de la présentation positive et de l’obstruction, ainsi que le retour exact à la présentation historique, sont réalisés. La génération positive relative à PositiveFormation est réalisée séparément au lot 2, suivie par q.positive-generation.

**Test proposé.** Modèles Unit/Bool sur le même parent positif ; quatre lois exactes du pont historique.

**Données reçues.** Chaîne relationnelle positive, jonction et enrichissements de pôles distincts.

**Constitution.** Séparation positive/obstruction et pont historique avec quatre retours déjà réalisés.

**Lectures dérivées.** Aucune occurrence périodique ni rejet de toute clôture déduit du parent positif.

**Portée constitutive.** Question répondue dans ces données, pas généralisation totale des formations.

**Reprise de l’analyse.** La génération relative réalisée possède son propre nœud ; elle ne redevient pas une lacune de la circularité positive.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Rôle final équipé de sa frontière

`q.equipped-final-role` · partial

La frontière avant choix, le rôle final par choix et la grammaire des rôles intérieurs/finals sont réalisés. La classification est exhaustive dans cette grammaire, avec retours et conservation des données par transport. La minimalité universelle et la rigidité générale restent ouvertes.

**Test proposé.** Modèles de frontière vide avant choix, deux jonctions avec unicité par choix, rôle extérieur dans une grammaire élargie, nœuds répétés et transports des témoins.

**Données reçues.** Forme, fibre, choix reçu ; grammaire intérieure/finale sur ce parent.

**Constitution.** Unicité par choix, classification exacte et transports des données déjà réalisés.

**Lectures dérivées.** La somme avec Unit classe cette grammaire ; le parent restitue les témoins ; elle ne classe pas une extension arbitraire.

**Portée constitutive.** Acquis T2 relatifs au parent ; extensions de rigidité/minimalité séparées.

**Reprise de l’analyse.** Marquer le rôle équipé acquis ; minimalité universelle optionnelle et non condition préalable à l'exhaustivité intérieure.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Transport de la constitution relationnelle

`q.rich-transport` · partial

Toutes les fibres ont des transports exacts avec calcul dépendant et restriction choisie. Les épines, positions et ordre sont transportés ; une formation reconstruite sur les mêmes états et pas conserve exactement ses histoires et commute avec déploiement, composition et clôture.

**Test proposé.** Modèles de fibres Unit/Empty sur mêmes sortes, échanges de jonction/provenance, données supplémentaires de pas conservées, ordre et clôture transportés.

**Données reçues.** Cartes exactes de toutes les fibres et accords des choix ; formation source.

**Constitution.** Calcul dépendant, épines, positions, relations et reconstruction sur mêmes State/Step déjà réalisés.

**Lectures dérivées.** Step entier gardé dans histoires ; données de pôles/obstruction et formations arbitraires non comparées.

**Portée constitutive.** Question partiellement répondue dans la signature et la reconstruction définies.

**Reprise de l’analyse.** Confirmer les acquis et localiser précisément les extensions ; ne pas dire qu'il manque encore tout transport relationnel.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Réalisation choisie et rigidité

`q.rigidity` · open

Comment séparer une réalisation exacte distinguée de la propriété selon laquelle toute réalisation admissible impose la même classification ?

**Test proposé.** Modèle avec deux réalisations possibles, puis interface optionnelle de rigidité et théorème de classification.

**Données reçues.** Famille Realizes et décomposition choisie à préciser pour la généralisation.

**Constitution.** L'instance historique dérive déjà l'injectivité et ses accords depuis le curseur ; inverse d'un placement fixé unique.

**Lectures dérivées.** Deux retours n'imposent pas seuls rigidité d'une relation Realizes arbitraire.

**Portée constitutive.** Question ouverte générale, acquise partiellement dans l'instance forte.

**Reprise de l’analyse.** Reformuler à partir de ces acquis : comparer quelles réalisations de quelle famille, avec quelles hypothèses ?

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Plusieurs témoins ou successeurs

`q.multiple-generation` · open

Le mécanisme du tournant peut-il être formulé sur une génération générale à plusieurs successeurs tout en conservant la continuation choisie ?

**Test proposé.** Construire deux successeurs non identifiés et coupler le certificat à l’un d’eux ; ne pas réutiliser implicitement la détermination par curseur.

**Données reçues.** Formation ramifiée et éventuellement continuation choisie, pas génériques.

**Constitution.** Deux successeurs distincts déjà modélisés ; couplage du tournant à une branche reste à construire.

**Lectures dérivées.** La sélection n'est pas déterminisme ; la progression canonique ne se transfère pas au Step arbitraire.

**Portée constitutive.** Question ouverte sur tournant couplé, pas possibilité de ramification.

**Reprise de l’analyse.** Conserver ouverte avec test branche par branche, même continuation, recomposition, résidu et admission explicite.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Quantité structurelle générale

`q.quantity` · open

Les correspondances intérieures exactes, les lectures de liens, l’ordre et la succession sont déjà formalisés. Quelle signature commune et quel critère d’équivalence empaquettent cette quantité structurale pour comparer des constitutions au-delà de leur seul porteur ou nombre ?

**Test proposé.** Empaqueter positions, occurrences, retours, liens et relations déjà établis ; comparer deux constitutions de même longueur aux relations ou témoins différents et vérifier les accords de leurs morphismes.

**Données reçues.** Positions, occurrences, réalisation exacte, liens, ordre et transports déjà acquis.

**Constitution.** Assemblage en quantité intérieure et critère général de comparaison encore à préciser.

**Lectures dérivées.** Le cardinal seul oublie relations/témoins ; le manque d'empaquetage n'est pas absence de quantité intérieure.

**Portée constitutive.** Question ouverte d'interface de comparaison relative à une signature choisie.

**Reprise de l’analyse.** La question vise l’assemblage et la comparaison de quantités intérieures déjà constituées, sans présenter leur structure existante comme absente.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Converse d’une reconstruction de trace

`q.converse-traces` · open

Sous quelles hypothèses supplémentaires une trace localement exacte, ordonnée et contiguë se reconstruit-elle en histoire enracinée composable ?

**Test proposé.** Définir précisément la contiguïté, tester les séparateurs puis fournir raccords source/cible et racine ; établir la propriété dans les deux sens.

**Données reçues.** Exactitude locale, ordre et contiguïté à définir ; racine et extrêmes à fixer.

**Constitution.** Reconstruction forte déjà acquise sur RootedGeneratedHistory ; converse générique non établie.

**Lectures dérivées.** Trace peut oublier raccord de source/cible, couverture des ponts et données initiales/finales.

**Portée constitutive.** Question ouverte de converse sur interfaces affaiblies.

**Reprise de l’analyse.** Garder la porte ; exiger les ponts effectifs et la couverture avant une promesse de reconstruction.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Fidélité des cibles sous interprétation

`q.concrete-faithfulness` · open

Quelles hypothèses sur ConcreteContinuationAlgebra préservent la distinction de la cible fermante et de la continuation libre ?

**Test proposé.** Construire ou récupérer une algèbre concrète qui fusionne les lectures, puis ajouter l’accord suffisant de séparation.

**Données reçues.** Algèbre concrète et lectures concernées ; aucune injectivité générale reçue.

**Constitution.** Transport exact d'occurrences déjà acquis ; séparation de cibles après lecture reste à caractériser.

**Lectures dérivées.** Égalité d'une lecture ne compare pas les constitutions ; l'interface actuelle ne fournit pas cette injectivité.

**Portée constitutive.** Question ouverte sur fidélité de certaines lectures.

**Reprise de l’analyse.** Nommer la lecture et l'accord suffisant ; ne pas annoncer un nouveau contre-modèle global sans code vérifié.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Algèbre de génération positive générale

`q.positive-generation` · answered

Une PositiveFormation reçue engendre des histoires finies composables et leur épine, avec nœuds, positions et lectures de compatibilité exacts. Une jonction distincte ferme la chaîne positive ; elle ne se déduit pas de la positivité seule.

**Test proposé.** Quatre modèles : chaîne dirigée sans clôture, chaîne fermée, deux successeurs admissibles, nœud brut répété avec positions distinctes.

**Données reçues.** PositiveFormation, nœuds équipés, Step, compatibilité et éventuels témoins de clôture.

**Constitution.** Histoires, composition, déploiement, positions et accords exacts déjà réalisés.

**Lectures dérivées.** Step peut avoir du contenu oublié par deploy ; aucune disponibilité générale ni clôture dérivée.

**Portée constitutive.** Question answered dans cette signature ; pas auto-génération des primitives.

**Reprise de l’analyse.** Confirmer ; remplacer généralité absolue par construction relative aux pas et témoins concrets reçus.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

## Pistes T6 — spéculation explicite

### Comparer les frontières par des morphismes équipés

La piste est réalisée T2 pour la frontière sélectionnée, les familles complètes et les opérations de la formation reconstruite. Les comparaisons entre formations arbitraires restent spéculatives.

**Test.** Étendre la signature et chercher des séparateurs des accords manquants.

**Données reçues.** Frontières, fibres complètes, choix et formation source.

**Constitution.** Résultats T2 des transports sélectionnés et reconstruction déjà établis.

**Lectures dérivées.** Comparer des formations arbitraires ou davantage d'opérations demeure distinct.

**Portée constitutive.** Piste T6 résiduelle pour extensions ; parties testées rattachées aux T2.

**Reprise de l’analyse.** Conserver la piste avec renvoi aux acquis précis ; ne pas appeler tout le programme spéculatif.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Propriété universelle des histoires

Une propriété universelle de chemins libres pourrait clarifier la reconstruction et le transport de la génération ; elle n’est pas établie ici.

**Test.** Définir les morphismes compatibles aux pas et prouver une extension unique point par point dans le cadre constructif.

**Données reçues.** Classe de morphismes et algèbres encore à définir.

**Constitution.** Aucune universalité générale établie ; récursions et lois opérationnelles existantes.

**Lectures dérivées.** Le mot libre et une interprétation de générateurs ne prouvent pas seuls extension unique dans toute catégorie.

**Portée constitutive.** Piste T6, pas théorème ni préalable à l'intérieur actuel.

**Reprise de l’analyse.** Confirmer son statut ; test : définition des morphismes puis extension unique point par point avec accords.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

## Méthodes et provenance

### Relations premières et présentation équipée

`m.presentation`

LocalNode et PerimeterSpine portent les témoins internes et successifs. PositiveCircularPresentation reçoit une chaîne positive et sa jonction ; l’obstruction est ajoutée séparément, et CircularPresentation garde l’interface historique.

**Portée.** Les supports et familles sont reçus ; les positions et le domaine intérieur sont constitués à partir des témoins internes et successifs. L’ordre des champs Lean ne décide pas de cette priorité.

**Données reçues.** Sortes-supports, familles, nœuds équipés, épine positive et jonction ; obstruction séparée.

**Constitution.** Positions here/later sur les avancées et couches de présentation raccordées.

**Lectures dérivées.** Nœuds et jonction peuvent être lus ; ces lectures ne constituent pas une occurrence intérieure.

**Portée constitutive.** Architecture relative aux primitives reçues ; pas auto-engendrement de toutes les sortes.

**Reprise de l’analyse.** La réception de supports et de témoins est distinguée de la constitution des positions et du domaine intérieur.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Noyau consommé de la détermination résiduelle

`m.core`

ResidualDeterminationCore conserve le nouvel étiquetage injectif et l’exclusion des labels internes ; le rôle résiduel est contractile.

**Portée.** Aucune ancienne occurrence ni loi de retour de la réalisation interne dans cette interface.

**Données reçues.** Étiquetage nouveau injectif, exclusion intérieure, rôle contractile.

**Constitution.** Détermination de l'étiquette résiduelle et unicité des nouvelles occurrences.

**Lectures dérivées.** Anciennes occurrences et inverse intérieur sont absents du noyau ; ce manque est un oubli délibéré.

**Portée constitutive.** Noyau abstrait de segmentation ; aucune description exhaustive du périmètre.

**Reprise de l’analyse.** Confirmer et situer après l'intérieur exact, sans confondre dépendance logique minimale et constitution complète.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Histoire enracinée et composable

`m.history`

History.Occurrence individue un pas dans une histoire précise. RootedGeneratedHistory conserve l’enracinement et la composition des pas GeneratedStep.

**Portée.** Les occurrences sont individuées dans une histoire constituée ; la lecture d’un même nœud ne les identifie pas. Les dépendances du graphe restent sélectionnées, sans extraction exhaustive des termes de preuve.

**Données reçues.** Famille Step et témoins concrets ; générateur historique et racine pour RootedGeneratedHistory.

**Constitution.** Histoires dépendantes, occurrences last/earlier et raccord des pas.

**Lectures dérivées.** Lectures source/cible/curseur après constitution ; leur codomaine ne remplace pas l'histoire.

**Portée constitutive.** Histoire générique et instance canonique à distinguer.

**Reprise de l’analyse.** L’individuation par construction devient centrale ; la réserve sur les dépendances sélectionnées reste explicite.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Fondations initiales de main : archive

`src.main`

Quatre modules fondationnels et leur façade publique, relus à la révision 8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685.

**Portée.** Snapshot et première carte conservés ; les ancrages de la carte active sont ceux de l’arbre de travail courant.

**Données reçues.** Sources et façade de la base 8a5e494, snapshots et contrôles antérieurs.

**Constitution.** Architecture historique déjà formalisée ; cette fiche n'ajoute aucune construction.

**Lectures dérivées.** Ancres de la base et état courant distingués ; l'archive ne vaut pas nouvelle validation.

**Portée constitutive.** Provenance historique des quatre modules ; hors certification nouvelle du dépôt.

**Reprise de l’analyse.** Conserver l'archive et placer ses résultats intérieurs au centre de la nouvelle lecture ; ne pas changer le tier de leurs nœuds.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Plan de reconstruction : propositions

`src.plan`

Plan de reconstruction désormais versionné dans la livraison bf13840. Sa référence du 30 septembre et ses interfaces proposées sont distinguées des déclarations effectivement réalisées dans les sources.

**Données reçues.** Texte conceptuel utilisateur, choix proposés et référence documentaire locale.

**Constitution.** Interfaces schématiques et critères futurs, pas des théorèmes compilés par ce document.

**Lectures dérivées.** La convention 0-types décrit les identités ; elle ne postule pas une extension d'unités primitivement individuées.

**Portée constitutive.** Programme relatif à une présentation ; statut documentaire et prospectif.

**Reprise de l’analyse.** Confirmer son statut de proposition ; remplacer toute lecture extensionnelle par relations, places, occurrences, domaine exact puis nombre éventuel.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Extension positive : provenance historique

`src.positive-worktree`

Extension positive initiale, relue avant commit sur la base 8a5e494, puis incluse dans la livraison bf13840 ; empreintes et contrôles historiques conservés.

**Portée.** Itération positive initiale archivée dans evidence/iterations/positive-selected-boundary ; ses résultats restent applicables. Le lot 1 a son propre snapshot et ses journaux.

**Données reçues.** Sources, empreintes et journaux de l'itération sur base 8a5e494.

**Constitution.** Présentation positive, pont et transports initiaux déjà produits.

**Lectures dérivées.** Date et mention non committée appartiennent à l'archive, pas nécessairement à HEAD livré.

**Portée constitutive.** Provenance d'une itération passée ; contrôles rapportés non répétés ici.

**Reprise de l’analyse.** Conserver les empreintes ; actualiser seulement le récit courant de livraison hors snapshot gelé.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Lot 1 : frontière avant jonction choisie

`src.closing-worktree`

Lot 1 relu avant commit : deux modules, trois modèles, 43 audits, build 106 et contrôle de 109 fichiers Lean. Sources incluses depuis dans bf13840.

**Portée.** Lot 1 archivé dans evidence/iterations/closing-choice-lot1 ; sa carte, ses empreintes et ses captures sont conservées.

**Données reçues.** Deux modules, modèles et contrôles antérieurs de lot 1.

**Constitution.** Forme, pointage, retours et distinctions existence/choix déjà réalisés.

**Lectures dérivées.** Mentions sans commit et nombres de tâches sont historiques.

**Portée constitutive.** Provenance de lot 1 ; aucune revalidation nouvelle.

**Reprise de l’analyse.** Conserver archive et hashes ; présenter les acquis depuis l'état livré sans réécrire l'histoire.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Lot 2 : formation et génération positives

`src.generation-worktree`

Lot 2 relu avant commit : trois modules, 79 audits, quatre modèles, build 109 et contrôle de 112 fichiers Lean. Sources incluses depuis dans bf13840.

**Portée.** Lot 2 archivé dans evidence/iterations/positive-generation-lot2 ; empreintes, carte et captures conservées.

**Données reçues.** Trois modules, modèles, empreintes et contrôles de lot 2.

**Constitution.** Histoires et déploiement avec positions/occurrences exactes déjà réalisés.

**Lectures dérivées.** Sources non committées décrivent l'itération archivée, pas nécessairement l'état courant.

**Portée constitutive.** Provenance de lot 2 ; pas nouvelle compilation.

**Reprise de l’analyse.** Conserver les traces et orienter le récit courant vers les constructions intérieures acquises.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Lot 3 : signature complète et formation reconstruite

`src.transport-worktree`

Lot 3 relu avant commit : sept modules, 162 audits, modèles de fibres et opérations, build 116 et contrôle de 119 fichiers Lean. Sources incluses depuis dans bf13840.

**Portée.** Lot 3 archivé dans evidence/iterations/signature-transport-lot3 ; carte, empreintes et captures conservées.

**Données reçues.** Sept modules, modèles et contrôles antérieurs de lot 3.

**Constitution.** Transports de fibres, épines, positions et formation reconstruite déjà réalisés.

**Lectures dérivées.** État non committé et compteurs appartiennent à l'archive.

**Portée constitutive.** Provenance de lot 3 ; pas validation nouvelle ou globale.

**Reprise de l’analyse.** Conserver les empreintes et rattacher les transports à la quantité intérieure constituée.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

### Lot 4 : sources livrées et revues conservées

`src.roles-worktree`

Lot 4 livré dans bf13840 : cinq modules, 109 audits, classification relative et modèles, build 121 et contrôle de 124 fichiers Lean. Le snapshot figé conserve le contexte de revue avant commit.

**Données reçues.** Cinq modules, modèles, audits et contrôles antérieurs de lot 4.

**Constitution.** Classification, ponts et transports des rôles déjà produits.

**Lectures dérivées.** Sources figées de pré-livraison et état Git courant sont des niveaux de provenance distincts.

**Portée constitutive.** Provenance de lot 4 ; sans validation computationnelle nouvelle.

**Reprise de l’analyse.** Conserver l'archive ; nouvelle analyse conceptuelle séparée du snapshot et de la revue formelle.

**Revue constitutive distincte.** refereed — Lecture constitutive acceptée au périmètre déclaré par un referee IA indépendant ; corrections intégrées, preuve et tier inchangés. Vérification humaine en attente.

## État des questions suivi

| Question | Statut |
|---|---|
| Correspondance exacte positions–occurrences | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Occurrences et positions du déploiement avec deux retours | T2 · Lean compilé ; referee IA indépendant (referee-positive-generation) ; humain en attente |
| Injectivité, ordre et adjacence dans une histoire réelle | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Factorisation constructive par le périmètre | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Grammaire et classification exactes des rôles équipés | T2 · Lean compilé ; referee IA indépendant (referee-circular-roles) ; humain en attente |
| Marqueurs historiques et accords de réalisation | T2 · Lean compilé ; referee IA indépendant (referee-circular-roles) ; humain en attente |
| La branche finale ne crée aucune position engendrée | T2 · Lean compilé ; referee IA indépendant (referee-circular-roles) ; humain en attente |
| Lecture numérique dérivée des histoires | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Présentation positive et obstruction séparées | T2 · Lean compilé ; referee IA indépendant (referee-positive-foundations) ; vérification humaine en attente |
| Déploiement depuis une formation positive reçue | T2 · Lean compilé ; referee IA indépendant (referee-positive-generation) ; humain en attente |
| Composition des histoires et réindexation du déploiement | T2 · Lean compilé ; referee IA indépendant (referee-positive-generation) ; humain en attente |
| Clôture explicite du déploiement positif | T2 · Lean compilé ; referee IA indépendant (referee-positive-generation) ; humain en attente |
| Enrichissement historique après la génération positive | T2 · Lean compilé ; referee IA indépendant (referee-positive-generation) ; humain en attente |
| Continuation choisie distincte de l’admissibilité des pas | T2 · Lean compilé ; referee IA indépendant (referee-positive-generation) ; humain en attente |
| Reconstruction exacte de la présentation historique | T2 · Lean compilé ; referee IA indépendant (referee-positive-foundations) ; vérification humaine en attente |
| Extraction autoritative de la frontière de clôture | T2 · Lean compilé ; referee IA indépendant (referee-positive-foundations) ; vérification humaine en attente |
| Frontière sans jonction et reconstruction exacte | T2 · Lean compilé ; referee IA indépendant (referee-closing-boundary) ; vérification humaine en attente |
| Témoin concret, pointage exact et habitation propositionnelle | T2 · Lean compilé ; referee IA indépendant (referee-closing-boundary) ; vérification humaine en attente |
| Une fibre fermante vide interdit le choix et son rôle | T2 · Lean compilé ; referee IA indépendant (referee-closing-boundary) ; vérification humaine en attente |
| Rôle habité et unique pour chaque jonction choisie | T2 · Lean compilé ; referee IA indépendant (referee-closing-boundary) ; vérification humaine en attente |
| Deux choix distincts malgré l’unicité du rôle par choix | T2 · Lean compilé ; referee IA indépendant (referee-closing-boundary) ; vérification humaine en attente |
| Accord des applications directes et unicité de l’inverse | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Calcul constructif des transports équipés de frontière | T2 · Lean compilé ; referee IA indépendant (referee-positive-foundations) ; vérification humaine en attente |
| Rôle final équipé et ses retours exacts | T2 · Lean compilé ; referee IA indépendant (referee-positive-foundations) ; vérification humaine en attente |
| Transports exacts de chaque fibre relationnelle | T2 · Lean compilé ; referee IA indépendant (referee-signature-transport) ; humain en attente |
| Calcul dépendant des transports complets | T2 · Lean compilé ; referee IA indépendant (referee-signature-transport) ; humain en attente |
| Restriction complète vers la frontière choisie | T2 · Lean compilé ; referee IA indépendant (referee-signature-transport) ; humain en attente |
| Transport des nœuds, épines et lectures de liens | T2 · Lean compilé ; referee IA indépendant (referee-signature-transport) ; humain en attente |
| Positions exactes, précédence et succession conservées et réfléchies | T2 · Lean compilé ; referee IA indépendant (referee-signature-transport) ; humain en attente |
| Reconstruction de formation et histoires entières exactes | T2 · Lean compilé ; referee IA indépendant (referee-signature-transport) ; humain en attente |
| Formation, composition et déploiement commutants | T2 · Lean compilé ; referee IA indépendant (referee-signature-transport) ; humain en attente |
| Clôture et frontière équipée de la chaîne transportée | T2 · Lean compilé ; referee IA indépendant (referee-signature-transport) ; humain en attente |
| Transport exact des positions et liens des rôles intérieurs | T2 · Lean compilé ; referee IA indépendant (referee-circular-roles) ; humain en attente |
| Cinq données choisies du rôle final conservées | T2 · Lean compilé ; referee IA indépendant (referee-circular-roles) ; humain en attente |
| Branches et classification conservées par transport | T2 · Lean compilé ; referee IA indépendant (referee-circular-roles) ; humain en attente |
| Unicité résiduelle du noyau | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Reconstruction interne sous conditions supplémentaires | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Classification et sortie du régime abstrait | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Continuation positivement engendrée et stricte | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Absence de retour dans une histoire générée positive | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Toute continuation positive fidèlement classée a un résidu unique | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Maximalité relative au régime circulaire | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Admission et satisfaction : adéquation démontrée | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Certificat du tournant périmétral affirmatif | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Interprétation exacte des occurrences concrètes | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Séparateur existant : exactitude locale sans ordre | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Séparateur existant : ordre sans pont composable | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Nouveau contre-modèle : retirer la fidélité détruit l’unicité | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Nouveau contre-modèle : transport exact sans conservation de l’ordre | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Diagnostic : le rôle final nu est uniformément ponctuel | T2 · Lean compilé ; referee IA indépendant (referee-foundations) ; vérification humaine en attente |
| Nouveau contre-modèle : positivité sans reconstruction intérieure | T2 · deux constructions Lean ; referee IA et contrôle du coordinateur ; vérification humaine en attente |
| Une bijection de fibre peut perdre la jonction choisie | T2 · Lean compilé ; referee IA indépendant (referee-positive-foundations) ; vérification humaine en attente |
| L’accord de jonction ne conserve pas la provenance | T2 · modèle du referee, relecture indépendante par le coordinateur ; Lean compilé ; vérification humaine en attente |
| La présentation positive autorise un retour du nœud brut | T2 · Lean compilé ; referee IA indépendant (referee-positive-foundations) ; vérification humaine en attente |
| Génération positive sans clôture disponible | T2 · Lean compilé ; referee IA indépendant (referee-positive-generation) ; humain en attente |
| Retour de nœud brut sans fusion des positions | T2 · Lean compilé ; referee IA indépendant (referee-positive-generation) ; humain en attente |
| Mêmes sortes sans transport possible des fibres | T2 · Lean compilé ; referee IA indépendant (referee-signature-transport) ; humain en attente |
| Choix de jonction et extension de la grammaire restent possibles | T2 · Lean compilé ; referee IA indépendant (referee-circular-roles) ; humain en attente |
| Circularité positive autonome | Données positives, pont et génération relative réalisés T2 |
| Rôle final équipé de sa frontière | Lots 1 et 4 réalisés et relus ; minimalité universelle et rigidité ouvertes |
| Transport de la constitution relationnelle | Lots 3A/3B réalisés et relus ; formations arbitraires, pôles et obstruction ouverts |
| Réalisation choisie et rigidité | Question ouverte ; interface non acquise |
| Plusieurs témoins ou successeurs | Question ouverte ; interface non acquise |
| Quantité structurelle générale | Question ouverte ; interface non acquise |
| Converse d’une reconstruction de trace | Question ouverte ; interface non acquise |
| Fidélité des cibles sous interprétation | Question ouverte ; interface non acquise |
| Algèbre de génération positive générale | Lot 2 réalisé T2 et relu · formation relative, clôture conditionnelle |

## Première prochaine exploration

L’intérieur exact et ses accords structurels sont déjà établis. La prochaine exploration de quantité vise leur empaquetage général et la comparaison de constitutions, puis les formations arbitraires, les pôles et l’obstruction. Les questions de rigidité et de minimalité universelle restent distinctes. Une nouvelle source exige une nouvelle revue.

Aucun atlas taille × invariant n’est défini pour ce chantier architectural. `frontier.json` reste absent plutôt que de produire une fraction artificielle de questions résolues.
