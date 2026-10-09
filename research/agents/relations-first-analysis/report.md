# Relecture des fondations depuis la priorité relationnelle

Auteur : agent `relations_first_analysis` ; 9 octobre 2026. Référence de travail transmise : branche `codex/positive-circular-foundations`, HEAD `bf13840cd8f39269a77fa25a3b99260a2930230b`. Rapport d'analyse **sous revue**, sans nouveau théorème et sans promotion de tier.

## Conclusion principale

Le centre fondationnel est un domaine intérieur **constitué par une architecture relationnelle témoignée**, exactement réalisé par des occurrences d'une construction. Il n'est pas une extension d'objets individués qui recevrait ensuite des relations. Le code donne un contenu effectif à cette priorité : les avancées de l'épine exigent leurs témoins, les positions sont engendrées par ces avancées, les occurrences sont indexées par des histoires composables, et leurs lectures peuvent coïncider sans les identifier. Les correspondances exactes, les accords locaux et les transports riches rendent cette constitution comparable. La longueur en donne ensuite une lecture.

La carte actuelle contient déjà ces acquis et de nombreuses réserves justes. Son défaut principal est celui de la hiérarchie de lecture : elle commence par le noyau résiduel et consacre beaucoup de visibilité aux limites de porteurs oubliés, alors que le résultat à comprendre d'abord est la constitution exacte de l'intérieur. Les limites doivent rester attachées aux projections et aux signatures affaiblies qui les produisent. Elles ne sont pas des réfutations de la priorité relationnelle.

Les 58 nœuds T2 sont conservés dans leur portée ; les 14 réfutations visent des inférences précises et sont conservées avec cette restriction. Aucun résultat formel n'est déclaré faux dans ce rapport. Les neuf questions, deux pistes et autres nœuds sont tous examinés individuellement dans `assessment.json` : **93 IDs, aucun omis**. Une correction de la narration n'est pas une nouvelle preuve ni une revalidation globale du dépôt.

## Méthode et sources

J'ai lu le `SKILL.md` de Labyrinth et `references/codex.md` du paquet temporaire autorisé. J'ai lu les 93 énoncés avec leurs hypothèses, données consommées, notes, ancres et statuts ; les modules de `RelationalPerimeter/Constitution` ; les interfaces, producteurs, preuves et exemples fondationnels pertinents de `SegmentedResidualRole`, `AbstractSegmentedTurning`, `ExactTypeTransport` et `StrongPerimetralTurning` ; les sondes fondationnelles et positives référencées par la carte ; la documentation française de constitution, positionnement, génération, frontière, rôles et transports ; les plans de reconstruction et de poursuite ; les rapports et la provenance documentaire existants. La lecture des grands modules porte sur les déclarations et leurs dépendances nécessaires à l'analyse, et ne prétend pas à un nouvel audit de chacune des 9 011 lignes de `StrongPerimetralTurning`.

Le plan renvoie au texte conceptuel fourni par l'utilisateur, `C:/Users/frederick/.codex/attachments/263ad19d-ee81-4cd1-94b4-af8544d25f63/Pasted text.txt`. Je l'ai retrouvé et lu. Ses §§1, 18, 28–34 et 65 expriment précisément la priorité des relations et la constitution du domaine, avant cardinalisation. La convention « ensembles au sens de la théorie des types, c'est-à-dire 0-types » du §2 concerne le niveau d'identité retenu ; elle n'introduit pas une extension préconstituée comme primitive.

Les sources de chaque nœud et ses raccords à d'autres nœuds sont conservés dans l'évaluation. Les anciens logs et métadonnées de revue sont des preuves de contrôles antérieurs, pas des contrôles répétés dans cette session. Je n'ai effectué ni build, ni gros calcul, ni écriture canonique, ni opération Git de modification. La façade computationnelle et son document de portée ont été lus uniquement pour établir la limite des imports et du discours : **la couche computationnelle reste hors de cette carte fondationnelle et n'est pas validée ici**.

## Ce qui constitue l'intérieur

`LocalNode` n'est pas un atome nu : il réunit deux interfaces, une différence, sa provenance et une compatibilité interne. Dans `Primitives.lean:15`, ces données vivent ensemble, avec leurs indices. Elles peuvent être reçues dans une présentation ; leur réception ne les transforme pas en occurrence du périmètre.

`PerimeterSpine.advance` reçoit `Compatible node.implicit nextNode.explicit`. Une épine n'est donc pas simplement la liste extensionnelle de valeurs nodales. `NonClosingPosition` n'a aucun constructeur sur `boundary`, et possède `here` et `later` sur `advance` (`Primitives.lean:28`, `:71`). Chaque place successive est déterminée par une avancée particulière. `NonClosingPrecedes` et `NonClosingNext` construisent ensuite la précédence et la succession immédiate sans rang numérique. La chaîne et ses témoins peuvent être reçus, mais le domaine des positions découle de sa constitution inductive.

Une histoire reçoit des pas concrets raccordés par leurs indices : `History.root/extend` dans l'instance historique (`StrongPerimetralTurning.lean:1508`) et `PositiveHistory.nil/cons` dans la formation générique (`PositiveGeneration.lean:90`). Les occurrences sont définies relativement à cette histoire. Leurs constructeurs n'identifient pas deux positions parce qu'elles lisent le même état, nœud ou témoin. Le modèle répété (`PositiveGenerationExamples.lean:152` et suivantes) le confirme, et `CircularRoleTransportExamples.repeated_complete_links` renforce le point : même un **lien complet égal** ne fusionne pas deux rôles placés à des positions distinctes.

La correspondance entre occurrences et positions du déploiement dispose de deux retours (`PositiveGeneration.lean:173–201`). `deploy_link_exact` conserve le paquet complet source/cible/compatibilité, dont les nœuds conservent leurs différences, provenances et compatibilités internes. Le déploiement historique possède également deux retours positions–occurrences (`StrongPerimetralTurning.lean:3197`, `:3205`). Dans ce déploiement canonique, chaque occurrence intérieure est décodée et chaque position successive est réalisée. C'est une couverture exacte d'un domaine déterminé par la construction, non un simple constat d'égalité de tailles.

Sur une `RootedGeneratedHistory`, `RequirementOccurrenceAgreement` reçoit exactement l'accord de curseur source (`StrongPerimetralTurning.lean:3801`). Les accords d'état source, de cible et de pas situé sont reconstruits dans cette instance canonique. `ExactNonClosingRealization` reçoit cet accord à chaque position. Son injectivité, sa conservation de précédence et de succession immédiate sont alors **des théorèmes**, non trois axiomes ajoutés à une application (`:4040`, `:4084`, `:4115`). Sa factorisation reconstruit le périmètre comme facteur initial de l'histoire (`:4654`). Cette factorisation peut laisser un suffixe vide ou une continuation extérieure ; elle n'identifie pas une réalisation exacte de tous les rôles intérieurs à une couverture de toute histoire cible.

L'intérieur doit donc se lire dans l'ordre suivant : relations et témoins reçus ; architecture constituée ; places et occurrences différenciées ; réalisation et décodage exacts ; accords relationnels ; frontière et rôle final ; prolongement possible. L'ordre textuel des champs Lean n'est pas un argument philosophique pour renverser cette chaîne.

## Réception, construction, lecture et oubli

| Couche | Reçu | Construit ou dérivé | Lecture ou oubli |
|---|---|---|---|
| Présentation successive | Sortes, familles, nœuds équipés, témoins d'avancée | Épine avec son type de positions et leurs relations | Nœud initial/terminal, lien lu à une position |
| Formation positive | `State`, `node`, `Step`, lecture de compatibilité | Histoires finies, composition, déploiement, occurrences et retours | `deploy` oublie les données de `Step` absentes des nœuds/liens |
| Intérieur historique | Parent relationnel et générateur canonique | Déploiement, décodage, injectivité, ordre, adjacence, factorisation | Lectures arbitraires réindexées sur les occurrences |
| Frontière | Indices, différence et provenance choisis | Forme sans jonction ; pointage à partir d'un témoin reçu | Oublier le pointage retire la jonction, pas tous les choix |
| Rôles équipés | Même épine et même frontière pointée | Rôle à une position ; rôle final unique pour ce choix ; classification exacte | `classify` oublie les témoins au niveau du porteur ; `assemble` les restitue depuis le même parent fixé |
| Transport | Cartes exactes de sortes et de toutes les fibres, accords choisis | Nœuds, épines, positions, relations et reconstruction de formation | Les états/pas entiers sont conservés dans cette reconstruction ; une formation arbitraire n'est pas couverte |
| Régime | Règles d'admission et obstruction explicites | Classification et diagnostic d'une même continuation | Le rejet logique minimal peut oublier l'occurrence tout en restant situé par la chaîne riche |
| Nombre | Histoire déjà constituée | `History.length` par récursion ; bornes de préfixes | La valeur naturelle oublie les relations, témoins et identités des occurrences |

« Relations premières » ne veut pas dire « toutes les sortes et tous les témoins doivent être engendrés ». Les types-supports rendent les familles dépendantes formulables. Dans `PositiveFormation`, les états et nœuds peuvent être reçus ; les occurrences de l'histoire et les positions de son déploiement sont constituées. Un état reçu, un nœud lu, une position et une occurrence sont quatre données différentes.

## Quantité structurelle et cardinalité

La quantité intérieure est déjà substantiellement réalisée : un domaine de positions relationnelles, un domaine d'occurrences, une réalisation réversible, leurs accords et leurs relations structurales. La famille primitive et les lois de transport précisent ce que les comparaisons conservent. Les résultats `th.perimeter-exact`, `th.rooted-structure`, `th.positive-occurrence-positions`, `th.signature-position-order` et `th.equipped-interior-role-transport` sont centraux à cette lecture.

`History.length` (`StrongPerimetralTurning.lean:7037`) est une élimination numérique de l'histoire. La borne `admissible_length_le_perimeter` vient d'une preuve de préfixe, et non l'inverse. Dans les traces expérimentales, les occurrences sont représentées par `Fin trace.steps.length` : c'est une représentation propre à un objet affaibli, pas la définition primitive de l'intérieur constitutif. Le compteur `walk` pilote une itération choisie dans une interface supplémentaire ; il n'est pas la source de l'identité des occurrences.

Le manque de `q.quantity` ne doit donc pas être annoncé comme « absence de quantité structurelle ». Il reste à **assembler explicitement** les données existantes dans une interface de comparaison intérieure et à définir ses morphismes avec la portée choisie : accords de réalisation, fibres et témoins distingués, liens, ordre, adjacence, opérations et changements d'indices. Les calculs déjà établis sur les signatures, frontières, épines et formations reconstruites doivent être utilisés et non refaits sous un nom nouveau. Un transport vers des formations arbitraires et une théorie uniforme de signatures arbitraires sont des extensions distinctes.

Une cardinalisation explicite `Occurrence history ↔ Fin history.length`, si elle est souhaitée, est un raccord de porteurs après constitution. Elle ne doit pas devenir une condition préalable à la signification de la quantité. Le naturel seul ne restitue ni les témoins ni l'ordre ni les données complètes des pas. Le modèle `FormationTransportExamples.equal_spines_with_distinct_step_data` montre déjà que même le déploiement complet peut oublier des données conservées dans l'histoire ; l'oubli numérique est plus fort encore.

## Classification déclarée et nécessité

`CircularRole` construit une branche intérieure équipée et une branche finale équipée. Ses deux retours avec `NonClosingPosition P.perimeter ⊕ Unit` assurent une **classification exacte de cette construction**, et non une démonstration que tout rôle possible dans toute théorie est nécessairement l'un de ces deux types. Cette borne est correcte. Cependant, l'ajout artificiel d'un élément dans `CircularRole P ⊕ Unit` ne réfute pas une revendication d'exhaustivité intérieure qui a toujours été relative au système construit : le texte conceptuel §31 disait déjà « relativement à cette présentation ». Le séparateur doit montrer où l'annonce cesse de s'appliquer, et non laisser croire que les unités intérieures étaient arbitrairement postulées.

Pour le rôle final, trois niveaux sont séparés : forme et fibre fermante ; choix concret de jonction ; rôle adapté à ce choix. La fibre peut être vide ou multiple ; le rôle sur un choix fixé est unique. La classification finale par `Unit` n'engendre aucune occurrence intérieure. `generatedPosition final = none` exprime cette lecture de la grammaire. Le déploiement constitue positivement tout son intérieur, et la branche finale n'ajoute pas une avancée ; ce point vaut mieux qu'un argument fondé uniquement sur le nom d'un constructeur.

Les deux retours de classification ne prouveraient pas, à eux seuls, une rigidité de toute relation abstraite `Realizes`. La question `q.rigidity` demeure sur une telle généralisation. L'instance historique a déjà sa détermination par curseur et ses conséquences fortes ; il faut les montrer comme acquis, puis demander seulement l'interface générale effectivement manquante.

## Hypothèses exactes de sortie de régime

La séparation des couches positives et obstruées est acquise. Une même chaîne positive reçoit des lectures de pôles identifiés ou séparés (`Examples.lean:31–68`). La circularité positive ne fournit pas son obstruction. La clôture d'une histoire générique reçoit une jonction distincte : le modèle dirigé déploie un pas alors que la fibre fermante est vide. La disponibilité de pas ne garantit pas une clôture.

Le théorème abstrait reçoit une frontière, une continuation et une relation d'extension irréflexive ; un régime admet la frontière canonique et analyse tout candidat admis en égalité canonique ou tentative de totalisation ; cette tentative est rejetée (`AbstractSegmentedTurning.lean:28`, `:329–386`). L'égalité avec la frontière est alors la classification exacte du régime ; l'extension stricte est incompatible avec cette admission. L'argument ne réclame pas une impossibilité absolue de génération.

Dans l'instance historique, `CircularRefinement` reçoit une extension recomposable, un étiquetage fidèle préservant les places antérieures, les accords intérieurs et surtout `realizesFinal` (`StrongPerimetralTurning.lean:5771`). **Ce dernier champ oblige une continuation positive admise à fournir une tentative bilatérale à son interprétation de frontière.** Il n'est pas déduit du seul `finalJunction`. L'obstruction héritée de la racine rejette la contraction produite par cette tentative. Les accords de `ResidualFinalClosureInterpretation` identifient l'occurrence résiduelle à celle de la frontière ; cette identité couplée est un acquis. La réfutation logique finale peut néanmoins consommer seulement l'obstruction et la contraction, sans réutiliser l'occurrence. Cela ne vide pas la chaîne de son sens constitutif.

`oneStepAfterPerimeter` reste une histoire positivement constituée et exactement interprétable. Elle quitte ce régime et cette spécification sous leurs clauses propres. Deux pas peuvent continuer la génération tout en échouant à recevoir le même étiquetage fidèle à résidu contractile. Le no-return historique vient des curseurs stricts du générateur canonique ; `PositiveHistory` générique permet les retours d'état et ne reçoit pas cette loi.

## Corrections concrètes de la carte et des documents

Ces remplacements sont des propositions au coordinateur, à relire avant intégration. Ils ne demandent aucun changement de source Lean.

1. **Sous-titre de la carte** — remplacer la première caractérisation centrée sur la « grammaire relative des rôles équipés » par : « Constitution relationnelle du domaine intérieur : places et occurrences, réalisation exacte et quantité structurelle ; circularité, continuation et sortie conditionnelle de régime. T2 relus par IA, contrôle humain en attente. »

2. **Accueil et ordre des résultats** — présenter d'abord `m.presentation`, `m.history`, `th.positive-formation-deployment`, `th.positive-occurrence-positions`, `th.perimeter-exact`, `th.rooted-structure` et `th.factorization`. Situer ensuite rôles équipés, frontière, transports, résidu et régime. Conserver les ID et les ancres ; l'ordre de présentation n'est pas un graphe de nécessité minimale.

3. **`m.presentation.note`** — remplacer « données d'entrée typées, non un auto-engendrement des primitives » par : « La présentation reçoit ses sortes, familles et témoins ; les avancées relationnelles constituent les places successives. Les occurrences et leur domaine exact sont construits ensuite relativement à cette architecture. »

4. **`th.rooted-structure.hypotheses`** — préciser : « `ExactNonClosingRealization` dans une histoire enracinée de `GeneratedStep` canoniques ; l'accord primitif de curseur source reconstruit les accords d'états source/cible et de pas situé. » Les accords dérivés ne doivent pas être relus comme autant d'hypothèses indépendantes.

5. **`q.quantity.statement`** — remplacer la formulation qui pourrait laisser entendre un simple porteur par : « L'intérieur périmétral possède déjà positions constituées, occurrences et réalisation exacte avec accords structuraux. Comment assembler ces données dans une interface de quantité intérieure et comparer deux telles constitutions sous une signature et des lois de transport explicites ? » Test : deux réalisations de même lecture numérique mais de relations ou témoins différents ; déterminer les accords requis pour leur comparaison, sans postuler leur équivalence.

6. **`th.final-role-carrier` et `x.universal-role-exhaustiveness`** — maintenir leurs résultats, ajouter respectivement : « L'oubli du parent et des lois de conservation est la source du diagnostic ; l'équivalence du porteur ne réfute pas le rôle équipé. » Et : « L'extension explicite du type change le domaine de classification ; elle ne réfute pas l'exhaustivité du système relationnel construit par la présentation. »

7. **`q.equipped-final-role`** — marquer la grammaire, les retours et le transport du choix fixé comme acquis ; déplacer la minimalité universelle vers une extension optionnelle précisément formulée. La minimalité n'est pas une dette créée par le fait que le système est déclaré.

8. **Titres des archives `src.*-worktree` et références pré-livraison** — conserver les bases et hashes historiques ; distinguer « sources et contrôles de l'itération » de l'état courant livré. L'ancienne phrase « ajouts non committés » dans un document gelé ne décrit pas nécessairement HEAD. Ce point de provenance ne modifie aucun théorème.

Le texte conceptuel contient aussi deux annonces à ajuster localement. Aux §§22 et 64, une équivalence de la famille finale avec une famille constante peut garder la frontière comme paramètre ; il faut écrire que la **projection du porteur seul** ne restitue pas les données équipées ni leurs lois de transport, plutôt que prétendre qu'une équivalence vers `Unit` perd nécessairement tout index. Aux §§31 et 49, la classification par l'étiquette finale n'est pas un habitant d'une famille supplémentaire `RealizesFull final occurrence` sans pont construit. Le plan distingue déjà cette obligation. Ces réserves limitent des phrases précises, pas le principe de genèse relationnelle des unités.

## Manques réels et tests qui peuvent changer la carte

- **Quantité intérieure équipée.** Assembler les données existantes et leurs comparaisons sous la signature retenue ; établir les lois qui manquent réellement à cet assemblage. Ne pas présenter une nouvelle structure réunissant des théorèmes existants comme un résultat universel autonome.
- **Réalisation complète indépendante de sa seule classification.** Si l'on veut une famille `RealizesFull` couvrant les deux branches et une notion de réalisation finale, préciser ses constructeurs et ses accords. `none` et une étiquette suffisent à leurs lectures actuelles, pas à tout énoncé sur cette famille future. Tester que le déploiement intérieur ne possède pas de constructeur final, et raccorder une occurrence de continuation lorsque les données requises existent.
- **Rigidité générale.** Choisir la famille de réalisation et les applications comparées. Les retours fixent une correspondance et déterminent son inverse ponctuellement ; ils ne rendent pas toutes les correspondances admissibles égales. L'accord de curseur historique reste un acquis spécialisé.
- **Tournant ramifié.** Deux successeurs sont déjà permis. Il manque une chaîne couplée fixant une continuation choisie, sa recomposition, son résidu et les règles propres d'admission. Tester chaque branche ; ne pas transférer le no-return ni le successeur canonique à toute formation.
- **Converse des traces.** Précédence et contiguïté à elles seules ne reconstituent pas les raccords de pas, la racine, les extrêmes et la couverture. Exiger et tester ces données avant un théorème converse. Les séparateurs portent sur les traces affaiblies.
- **Interprétations concrètes plus fidèles.** Les retours d'occurrences ne garantissent pas l'injectivité des lectures d'états ou d'interfaces. Nommer la lecture que l'on veut séparer et l'accord ajouté. Ce rapport n'ajoute pas un contre-modèle Lean nouveau.
- **Comparaison de formations arbitraires, pôles et obstruction.** Les transports actuels reconstruisent une formation avec les mêmes `State` et `Step`, et ne transportent pas les opérations de pôles ou le rejet. Des accords supplémentaires explicites sont nécessaires si ces données entrent dans la comparaison.

`h.free-paths` demeure une piste T6 : une universalité demanderait sa classe d'interprétations, ses opérations et une extension unique définie et prouvée. Elle n'est ni déjà établie par le mot « libre », ni indispensable pour lire la constitution intérieure actuelle.

## Décision d'intégration proposée

Réorganiser le récit et les fiches autour du domaine intérieur constitué ; préserver les T2 et les contre-modèles limités à leurs signatures ; ajouter les précisions ci-dessus et reformuler les portes comme extensions d'acquis identifiés. Ne créer ni nouveau théorème universel, ni mesure de résolution, ni validation computationnelle. Le fichier `assessment.json` constitue la liste exhaustive des décisions proposées, sous revue indépendante.
