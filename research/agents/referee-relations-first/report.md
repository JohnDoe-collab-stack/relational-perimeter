# Relecture indépendante depuis les relations premières — phase 1

Date : 9 octobre 2026. Branche lue : `codex/positive-circular-foundations`. HEAD vérifié : `bf13840cd8f39269a77fa25a3b99260a2930230b`.

## Verdict et portée

**ESTABLISHED, dans les interfaces déclarées :** l'intérieur du périmètre est un domaine constitué de positions et d'occurrences, avec des correspondances à deux retours, des relations de précédence et de succession distinctes, et des lectures exactes des liens témoins. Ce domaine ne se réduit pas aux valeurs lues sur les supports primitifs. La clôture équipée constitue une autre branche : elle conserve une jonction reçue et n'ajoute aucune occurrence à cet intérieur.

**Aucun énoncé des 58 nœuds T2 n'est réfuté par cette reprise.** Je recommande de conserver leurs tiers et leurs scopes formels. La priorité relationnelle demandée par l'utilisateur appelle une autre organisation de l'analyse et une qualification séparée de l'adéquation conceptuelle ; elle ne justifie pas d'effacer des théorèmes exacts, des limites démontrées ou les vérifications antérieures.

**GAP :** une équivalence universelle de constitutions arbitraires, une minimalité universelle de la grammaire, une rigidité générale des réalisations et une théorie générale de quantité munie de son critère d'équivalence ne sont pas établies. Ces manques ne rendent pas absents le domaine intérieur exact, sa structure ou les transports équipés déjà construits.

Le point de départ « les relations sont premières et pas les objets » est ici traité comme l'intention mathématique de la constitution. L'ordre des champs `Explicit`, `Implicit`, `Compatible`, etc. est une dépendance de typage ; ce n'est pas une preuve de priorité ontologique des supports. Réciproquement, les fichiers ne produisent pas tous les éléments des sortes primitives à partir d'une relation sans données reçues. Ils constituent les objets étudiés — configurations, positions, occurrences, histoires et rôles — relativement à des familles, témoins et règles reçus. Les deux propositions suivantes sont donc incorrectes : « aucun objet n'est constitué parce que les types de support sont donnés » et « aucune donnée n'est reçue parce que la constitution est relationnelle ».

Cette phase relit les sources et la carte initiale des 93 nœuds. La carte et le document de reprise à produire par le coordinateur feront l'objet d'une seconde phase indépendante. Aucune modification canonique, mutation Git, exécution Lean ni construction globale n'a été faite par ce referee.

## Méthode et pièces indépendantes

J'ai lu le `SKILL.md` Labyrinth temporaire et `references/codex.md`, les sources des quatre modules initiaux, les interfaces et preuves pertinentes des modules `Constitution`, les modèles et les sondes auxquels la carte renvoie, puis les documents explicatifs et le plan original. Le rapport n'utilise pas un avis antérieur de referee comme preuve de son propre verdict.

`knowledge-baseline.json` conserve la carte examinée. Mon script `AuditCoverage.ps1`, écrit dans cette archive, contrôle indépendamment les IDs et les ancres, puis archive les déclarations concernées dans `source-excerpts.md`. Résultat : **93 IDs distincts, 184 références Lean, aucune ancre décalée**. `coverage.json` donne le détail. Ce contrôle textuel ne certifie pas le sens d'un théorème ni son acceptation par le noyau Lean.

Un calcul indépendant avec SHA-256 après normalisation CRLF→LF retrouve les **47 empreintes** du snapshot actif, avec **zéro différence** ; le résultat est dans `source-fingerprints.json`. Les journaux archivés portent les succès de compilation et des contrôles globaux des différentes itérations. Je les ai lus comme preuves historiques d'exécution ; je n'ai pas relancé Lean et ne prétends pas avoir produit une nouvelle compilation. Les résultats restent T2, avec vérification humaine en attente.

Dans les tableaux, `ESTABLISHED` qualifie une prétention établie au scope indiqué ; `FALSE` qualifie la prétention plus forte qui est réfutée, et non l'exactitude du texte « réfuté » de la carte ; `GAP` qualifie une prétention non établie. Un verdict conceptuel n'est pas un nouveau tier de preuve.

## Ce qui est reçu et ce qui est constitué

| Couche | Données effectivement reçues | Constitution et accords acquis | Projection ou limite |
|---|---|---|---|
| Signature primitive | Supports `Explicit`, `Implicit`, `Difference`, familles `Compatible` et `Provenance` dans `Type` | Fibres de témoins typées aux indices correspondants | Aucun domaine intérieur n'est égal par définition à l'ensemble de ces supports |
| Nœud | Termes explicite/implicite, différence, provenance, compatibilité interne | `LocalNode` est une configuration relationnelle équipée | Les valeurs seules oublient les témoins ; une égalité de lectures n'est pas une identité d'occurrences |
| Épine | Nœud initial et avancées avec leurs compatibilités successives | `NonClosingPosition` vient des constructeurs de l'épine ; `linkAt` lit le lien entier ; précédence et succession ont leurs propres constructeurs | Plusieurs positions peuvent lire le même nœud ou lien |
| Formation générale | `State`, lecture `node`, `Step source target`, lecture de compatibilité du pas | Une histoire de pas concrets est composable par ses indices ; `deploy` en construit l'épine et les accords début/terme/liens | La formation ne choisit pas d'elle-même un successeur et peut manquer de pas ; déployer oublie certains contenus de `Step` |
| Histoire et occurrences | Histoire fixée, contenant les pas concrets | Occurrences indexées par cette histoire ; deux retours avec les positions de son déploiement | Ce n'est pas une équivalence entre toutes les histoires et toutes les épines |
| Réalisation historique | Histoire enracinée à `GeneratedStep` canonique et carte `realize` ; accord du curseur source à chaque position | L'état source, le pas situé et la cible sont dérivés ; injectivité, précédence, adjacence et factorisation par le périmètre sont prouvées | L'histoire peut posséder un suffixe ; injectivité ne signifie pas exhaustivité de toutes ses occurrences |
| Frontière | Forme avec source/cible, différence et provenance ; puis jonction concrète si l'on veut pointer | La frontière équipée conserve le témoin ; le rôle final est unique sur ce choix fixé | La fibre avant choix peut être vide ou multiple ; pas de choix extrait de `Nonempty` vers `Type` |
| Rôles équipés | Même présentation, liens lus exactement aux positions, choix fermant fixé | Rôles intérieurs déterminés par leur position ; branches intérieure/finale distinctes ; classification à deux retours | Exhaustivité de `CircularRole P`, sans impossibilité universelle d'élargir la grammaire |
| Quantité intérieure | Domaine constitué et réalisation à deux retours | Quantité structurale exacte de cet intérieur, munie de ses liens, ordre et adjacence ; ces accords précèdent la lecture numérique pertinente | `History.length` ne fonde pas l'identité ; un objet général de quantité avec equivalences arbitraires reste à définir |
| Régime et obstruction | Règle d'admission, obligation de totalisation, refus de contraction | Classification exacte dans le régime ; une continuation positive demeure constituée et sort de ce régime | La sortie ne découle pas de la seule jonction ni de la seule circularité positive |
| Comparaison | Cartes avec deux retours ; accords des fibres et témoins nécessaires selon la signature | Transports de frontière, signature, positions, formation reconstruite, opérations et rôles | Une équivalence de porteurs n'est pas à elle seule un transport de constitution |

Le mot « reçu » ne dévalorise aucune de ces données : il indique l'autorité dont part une construction. La question pertinente est ce que ces données déterminent ensemble et ce que les accords reconstruisent. Le domaine intérieur constitué est celui de l'épine et de l'histoire fixées, et non tout `State`, tout `Explicit` ou tout `Implicit` possible.

## Raisonnement indépendant sur les points centraux

### Intérieur, identité et exactitude

Pour chaque constructeur `advance` d'une épine, `NonClosingPosition` dispose de `here`, et transporte les autres positions par `later`. Les identités des positions suivent donc la constitution de l'épine. La répétition d'un nœud ne supprime pas un constructeur `here` ou `later`. Le même raisonnement vaut pour les occurrences de `PositiveHistory` par `cons`, et pour celles de `History` par `extend`. Une lecture constante peut identifier des valeurs tout en laissant ces occurrences distinctes.

Les cartes récursives positions↔occurrences ont deux retours. Cela donne l'exhaustivité exacte sur **le déploiement fixé**, sans recours à un compte numérique. Les relations d'ordre et de succession sont établies ou transportées séparément. On possède donc davantage qu'une simple égalité de cardinalité.

Dans `ExactNonClosingRealization`, l'adjectif « exact » s'applique à la réalisation de chaque exigence dans une histoire enracinée. Le champ primitif de `RequirementOccurrenceAgreement` est seulement `sourceCursorExact` (`StrongPerimetralTurning.lean:3801`). Le générateur canonique et l'enracinement permettent de reconstruire la totalité du pas situé. Les preuves d'injectivité et d'ordre utilisent ensuite l'irréflexivité des futurs de curseur : identifier deux positions ou renverser leur ordre obligerait un futur strict à revenir à lui-même. L'adjacence utilise l'égalité du terme du premier pas à la source du second ; un interstice positif donnerait la même contradiction. Ce raisonnement ne s'étend pas à la trace affaiblie qui a oublié la composition.

La factorisation reconstruit un suffixe, éventuellement vide. Par conséquent, le mot « exact » ne donne pas automatiquement une surjection vers toutes les occurrences d'une histoire plus longue. Les limites écrites dans la carte et dans le pont historique sont justes et doivent être maintenues.

### Clôture sans occurrence supplémentaire

`deployRemaining` suit les avancées successives et s'arrête sur `boundary`. `PositiveHistory.deploy` fait de même à partir des pas. Aucun des deux ne transforme la jonction fermante en pas. La jonction est un témoin de la fibre terminal-implicite→initial-explicite ; le pas libre supplémentaire a sa propre cible formée. Leurs indices et leurs producteurs sont différents.

`generatedPosition final = none` et `realizeRole final = none` constatent le choix de la grammaire et de sa lecture. C'est une garantie exacte de cette classification, pas une preuve indépendante que toute théorie concevable devrait traiter la clôture de cette façon. L'adéquation au projet tient au raccord explicite à la même présentation et à ses témoins, avec transports qui préservent ce choix.

Le diagnostic `FinalRequirement P ≃ Unit` reste correct. Il montre que le marqueur nu n'emporte pas seul la jonction. Il ne rend pas vide la frontière qui indexe `EquippedFinalRole`, ni ses cinq accords de transport. Le pont reconstruit le rôle équipé depuis **le même parent P** ; sans ce parent, le marqueur n'a pas les données nécessaires à la lecture de la jonction.

### Résidu, génération, obstruction et régime

La preuve résiduelle est élémentaire et valide : exclusion des étiquettes intérieures → étiquette résiduelle ; contraction du résidu → même étiquette ; injectivité de l'étiquetage → même occurrence. La positivité fournit ensuite un habitant. Ce raisonnement établit une unicité conditionnelle, pas une création de toute partie nouvelle ni une reconstruction automatique de l'ancien intérieur. Le contre-modèle à `embedOld` non injectif est donc compatible avec l'unicité résiduelle.

La couche générale positive reçoit des pas admissibles et permet plusieurs successeurs. La couche historique `GeneratedStep` est une formation canonique stricte ; ses théorèmes de non-retour ne valent pas pour tous les pas de `PositiveFormation`. Le compteur de `walk` pilote une itération choisie. Il ne constitue pas les identités des occurrences.

`CircularRefinement.realizesFinal` impose la tentative bilatérale à la branche positive. L'obstruction de contraction rejette cette tentative. Ce sont des hypothèses et producteurs inspectables. La jonction seule ne produit ni cette obligation ni son rejet. Le certificat final assemble une construction effective et la classification relative du régime ; l'assemblage seul ne démontrerait pas une causalité philosophique supplémentaire. L'histoire peut continuer librement alors que l'admission est impossible.

### Comparaison des constitutions

`ExactTypeTransport` garantit deux applications et leurs retours. Il ne reçoit pas de relation à conserver. L'involution de `Bool` illustre exactement la différence entre une équivalence de porteurs et un accord d'ordre. La même distinction s'applique aux témoins choisis : des cartes exactes de toutes les fibres peuvent échanger le témoin d'une jonction ou d'une provenance.

`BoundaryTransport` reçoit cinq accords sur les données choisies ; `ConstitutiveSignatureTransport` reçoit des transports de toutes les fibres aux indices transportés. La restriction vers une frontière demande encore les accords des témoins distingués. Ces obligations établissent une comparaison de la constitution choisie, au scope annoncé.

Les transports d'histoires conservent intégralement `State` et `Step` dans la formation reconstruite. Les deux retours des histoires sont valides, y compris pour les contenus de pas que le déploiement oublie. Ils ne constituent pas une comparaison de deux formations cibles arbitraires. Le transport des positions est au-dessus d'une épine source fixée ; il n'est pas annoncé comme équivalence générique de tous les types d'épines. Ces deux limites sont exactes, sans constituer une réfutation du programme relationnel.

## Examen des 93 nœuds

Les énoncés, hypothèses, résumés `consumed` et références ont été confrontés aux déclarations et producteurs. Pour les T2, `ESTABLISHED` signifie acceptation du contenu formel au scope de la carte, avec les preuves et logs archivés ; aucun nouveau run Lean n'est ajouté. Les résumés `consumed` décrivent des usages de la preuve présente, jamais la nécessité universelle de toutes les hypothèses. Les graphes de liens sont sélectionnés et ne doivent pas être lus comme une extraction exhaustive des termes de preuve.

| ID | Verdict exact, scope et correction éventuelle |
|---|---|
| `src.main` | **ESTABLISHED**, archive des quatre modules et de leur relecture à la base citée ; séparer cette base du HEAD livré. |
| `src.plan` | **ESTABLISHED**, plan proposé et référence du 30 septembre ; **FALSE au présent** pour « non suivi par Git » à HEAD, où `git ls-files` retourne ce document. Dater l'observation. |
| `m.presentation` | **ESTABLISHED**, nœuds/épine témoins et données positives reçues ; ne pas interpréter les supports de typage comme les objets primitifs étudiés. |
| `m.core` | **ESTABLISHED**, noyau sans anciennes occurrences, consommant exclusion, contraction et injectivité nouvelle. |
| `m.history` | **ESTABLISHED**, occurrences d'une histoire précise, enracinement et composition historiques. |
| `th.residual` | **ESTABLISHED T2**, unicité conditionnelle du nouvel intérieur résiduel ; positivité fournit l'habitant, pas l'injectivité. |
| `th.internal-reconstruction` | **ESTABLISHED T2**, `embedOld` injectif et positivité reconstruisent les deux retours de la complétion compatible au noyau. |
| `th.abstract-exit` | **ESTABLISHED T2**, classification et sortie depuis `classifyOrTotalize`, rejet et irréflexivité ; aucun effet de la seule circularité. |
| `th.transport-backward` | **ESTABLISHED T2**, unicité ponctuelle des inverses quand les cartes directes exactes s'accordent. |
| `th.perimeter-exact` | **ESTABLISHED T2**, deux retours et donc couverture exhaustive des occurrences du déploiement canonique, intérieur sans occurrence de jonction finale. |
| `th.rooted-structure` | **ESTABLISHED T2**, injectivité, ordre et adjacence historiques ; préciser que seul l'accord du curseur source est reçu et que les accords d'états/cible/pas sont dérivés. |
| `th.factorization` | **ESTABLISHED T2**, périmètre comme préfixe reconstructible et suffixe éventuellement vide ; pas de stricte positivité garantie. |
| `th.positive-continuation` | **ESTABLISHED T2**, continuation d'un pas du générateur historique libre et distinction stricte du déploiement. |
| `th.no-return` | **ESTABLISHED T2**, non-retour des `GeneratedHistory` positifs, par les curseurs ; scope historique canonique. |
| `th.labelled-residual` | **ESTABLISHED T2**, toute extension fidèlement étiquetée force les nouvelles occurrences au rôle final ; leur unicité ne crée pas l'étiquetage reçu. |
| `th.circular-classification` | **ESTABLISHED T2**, raffinement ↔ égalité au déploiement selon le régime choisi et son obstruction. |
| `th.specification` | **ESTABLISHED T2**, transformations dans les deux sens entre satisfaction et raffinement, sans identité des interfaces. |
| `th.turning` | **ESTABLISHED T2**, producteurs rassemblés dans le certificat ; le scope est celui de `CircularPresentation` et du régime historique. |
| `th.numeric-readout` | **ESTABLISHED T2**, borne de `History.length` depuis le préfixe admissible ; souligner la quantité structurale intérieure déjà exacte avant cette lecture. |
| `th.concrete-interpretation` | **ESTABLISHED T2**, correspondance exacte des occurrences de l'histoire concrète construite par l'algèbre ; aucune fidélité générale des valeurs/états lus. |
| `th.separator-order` | **ESTABLISHED T2**, trace permutée localement exacte et injective qui renverse la précédence ; trace affaiblie, pas histoire enracinée. |
| `th.separator-bridge` | **ESTABLISHED T2**, trace ordonnée intercalée sans pont composable effectif pour les occurrences intermédiaires indiquées. |
| `th.separator-injectivity` | **ESTABLISHED T2**, deux occurrences `Bool`, étiquette résiduelle constante, exclusion intérieure ; l'injectivité supprimée ne peut être récupérée. |
| `th.separator-transport` | **ESTABLISHED T2**, transport `Bool.not` exact qui ne préserve pas `Before`. |
| `th.final-role-carrier` | **ESTABLISHED T2**, rôle final nu exactement ponctuel ; diagnostic du marqueur, sans réfutation de la frontière équipée. |
| `x.local-order` | **FALSE**, exactitude locale⇒ordre sur toute trace ; séparation par permutation. |
| `x.order-bridge` | **FALSE**, ordre⇒participation composable ; séparation par intercalation. |
| `x.weak-unique` | **FALSE**, contraction/exclusion seules⇒unicité d'occurrences ; il manque l'injectivité. |
| `x.exact-order` | **FALSE**, équivalence de types⇒conservation de toute relation ; `Bool.not` suffit. |
| `q.positive-circle` | **ESTABLISHED**, séparation positive/obstruction et pont exact ; la génération du lot 2 est une réponse distincte déjà acquise, actualiser la note. |
| `q.equipped-final-role` | **ESTABLISHED**, frontière avant choix, rôles par choix et grammaire relative ; **GAP** pour minimalité universelle et rigidité générale. |
| `q.rich-transport` | **ESTABLISHED**, fibres, positions, ordre et formation reconstruite ; **GAP** pour comparaison des formations arbitraires et pôles/obstruction. |
| `q.rigidity` | **GAP**, rigidité générale entre réalisations admissibles ; ne pas la confondre avec les retours d'une réalisation fixée. |
| `q.multiple-generation` | **ESTABLISHED**, formation avec plusieurs successeurs ; **GAP** pour le tournant général couplé à une continuation choisie. |
| `q.quantity` | **GAP**, signature et équivalence générale de quantité ; **ESTABLISHED**, contenu structural de la quantité intérieure fixée et transports déjà prouvés. |
| `q.converse-traces` | **GAP**, reconstruction d'une trace localement exacte, ordonnée et contiguë en histoire ; les séparateurs existants ne prouvent pas cette converse. |
| `q.concrete-faithfulness` | **GAP**, loi générale de séparation des lectures des cibles ; exactitude des occurrences reste acquise. |
| `h.equipped-morphisms` | **ESTABLISHED**, volets précis de frontière/fibres/reconstruction ; **GAP T6**, comparaison de formations arbitraires. |
| `h.free-paths` | **GAP T6**, propriété universelle ; concaténation associative ne suffit pas à l'annoncer. |
| `th.separator-old-completion` | **ESTABLISHED T2**, deux variantes d'un plongement ancien effondré ; résidu unique mais aucune complétion à deux retours compatible au noyau. |
| `x.positive-old-completion` | **FALSE**, positivité⇒reconstruction exacte de l'ancien intérieur sans injectivité ancienne. |
| `th.positive-split` | **ESTABLISHED T2**, même parent positif avec lectures de pôles identifiés ou séparés ; obstruction uniquement pour le second modèle. |
| `th.circular-bridge` | **ESTABLISHED T2**, reconstruction exacte des champs et témoins historiques par quatre retours. |
| `th.boundary-extraction` | **ESTABLISHED T2**, extraction des cinq données choisies depuis le même parent positif ; aucune occurrence ajoutée. |
| `th.boundary-calculus` | **ESTABLISHED T2**, identité/inversion/composition et lois ponctuelles sur cinq porteurs et cinq accords ; scope sélectionné. |
| `th.equipped-role` | **ESTABLISHED T2**, rôle unique sur frontière pointée, retours et données conservées ; actualiser la limite historiquement relative à la grammaire alors future. |
| `th.separator-closing-witness` | **ESTABLISHED T2**, applications spécifiées qui échangent la jonction malgré les indices inchangés ; identité riche toujours possible. |
| `th.separator-provenance-witness` | **ESTABLISHED T2**, échange seulement de provenance, incompatibilité avec `provenanceExact` pour ces applications. |
| `th.separator-positive-recurrence` | **ESTABLISHED T2**, répétition du nœud brut ; sans retour du curseur historique ni périodicité d'exécution. |
| `src.positive-worktree` | **ESTABLISHED**, provenance de l'itération et logs build104/vérification107 ; « sources non committées » est historique, à dater. |
| `x.carrier-junction` | **FALSE**, équivalence des porteurs⇒conservation du témoin choisi. |
| `x.junction-provenance` | **FALSE**, conservation de jonction⇒conservation de provenance. |
| `x.positive-no-recurrence` | **FALSE**, présentation positive⇒absence de retour de nœud brut. |
| `q.positive-generation` | **ESTABLISHED**, histoire/épine et lectures exactes relatives aux pas reçus ; clôture séparément témoignée. |
| `th.closing-shape-bridge` | **ESTABLISHED T2**, oubli/reconstruction de forme, pointage et frontière avec retours exacts ; seuls la jonction et son choix sont omis par la forme. |
| `th.closing-pointing-exact` | **ESTABLISHED T2**, fibre de témoins↔pointages dans `Type`, habitation équivalente dans `Prop` ; pas de choix propositionnel vers donnée. |
| `th.closing-empty` | **ESTABLISHED T2**, vide direct avant choix interdit pointage et rôle sur pointage ; impossible comme oubli d'une frontière équipée. |
| `th.closing-role-choice` | **ESTABLISHED T2**, rôle habité et unique pour pointage fixé, accord exact avec sa jonction. |
| `th.closing-choice-multiplicity` | **ESTABLISHED T2**, deux choix `Bool` malgré unicité sur chacun ; `Unit` donne séparément une fibre unique. |
| `x.role-unique-choice` | **FALSE**, unicité par choix⇒unicité de tout choix. |
| `src.closing-worktree` | **ESTABLISHED**, itération du lot 1, 43 audits et logs build106/vérification109 ; « sans commit » est historique, à dater. |
| `th.positive-formation-deployment` | **ESTABLISHED T2**, déploiement conservant nœuds et compatibilité depuis les pas reçus ; pas d'injectivité générale sur les histoires. |
| `th.positive-history-composition` | **ESTABLISHED T2**, unités/associativité et déploiement composant avec `appendAlong` ; actualiser la note sur le transport des opérations maintenant réalisé au lot 3. |
| `th.positive-occurrence-positions` | **ESTABLISHED T2**, deux retours de toutes les occurrences du déploiement positif fixé ; distinction `here/later`. |
| `th.positive-explicit-closing` | **ESTABLISHED T2**, frontière extraite puis présentation fermée à partir de l'occurrence et de la jonction concrètes séparées. |
| `th.positive-generated-historical-bridge` | **ESTABLISHED T2**, enrichissement historique du même déploiement ; pas de transfert des lois strictes à tout `Step`. |
| `th.positive-successor-choice` | **ESTABLISHED T2**, continuation globale comme donnée supplémentaire ; itération choisie positive et modèles avec deux choix ou aucun. |
| `th.separator-generated-unclosed` | **ESTABLISHED T2**, histoire dirigée positive dont la fibre fermante est vide. |
| `th.separator-repeated-positive-occurrences` | **ESTABLISHED T2**, mêmes nœuds, occurrences/positions et témoins distincts ; retour d'état permis dans cette formation. |
| `x.generation-forces-closure` | **FALSE**, chaîne positive⇒jonction disponible. |
| `x.positive-unique-successor` | **FALSE**, admissibilité⇒successeur unique. |
| `x.repeated-nodes-merge-positions` | **FALSE**, mêmes lectures de nœud⇒même occurrence. |
| `src.generation-worktree` | **ESTABLISHED**, lot 2, 79 audits et logs build109/vérification112 ; « sources non committées » est historique, à dater. |
| `th.signature-fibre-transport` | **ESTABLISHED T2**, transports exacts reçus de toutes les compatibilités/provenances aux indices transportés ; pas de dérivation depuis les seules sortes. |
| `th.signature-calculus` | **ESTABLISHED T2**, calcul dépendant ponctuel ; inversion avec réindexation des fibres explicite. |
| `th.signature-boundary-restriction` | **ESTABLISHED T2**, restriction vers les cinq porteurs choisis, avec trois accords d'indices et deux accords de témoins. |
| `th.signature-spine-transport` | **ESTABLISHED T2**, épine, terme, composition et liens entiers transportés ; pas d'équivalence générique annoncée des types d'épines. |
| `th.signature-position-order` | **ESTABLISHED T2**, deux retours des positions et conservation/réflexion distinctes de précédence/succession. |
| `th.signature-formation-histories` | **ESTABLISHED T2**, retours des histoires/occurrences dans la formation reconstruite sur mêmes `State` et `Step`, contenus de pas conservés. |
| `th.signature-formation-operations` | **ESTABLISHED T2**, composition/déploiement/liens/positions et marche choisie raccordés ; sélection du successeur reçue. |
| `th.signature-closing-transport` | **ESTABLISHED T2**, fibre fermante et données choisies de la présentation transportées ; actualiser la note sur la classification du lot 4 maintenant réalisée. |
| `th.separator-sort-fibres` | **ESTABLISHED T2**, mêmes sortes mais `Unit`/`Empty` dans les fibres ; aucun transport complet. |
| `x.sort-transport-fibres` | **FALSE**, bijections des sortes⇒transport de toutes les familles. |
| `src.transport-worktree` | **ESTABLISHED**, lot 3, 162 audits et logs build116/vérification119 ; « sources non committées » est historique, à dater. |
| `th.equipped-circular-classification` | **ESTABLISHED T2**, rôles intérieurs équivalents aux positions équipées et classification circulaire à deux retours ; exhaustivité relative. |
| `th.final-role-no-occurrence` | **ESTABLISHED T2**, lecture de branche finale sans position/occurrence intérieure ; résultat de cette grammaire et de cette lecture. |
| `th.equipped-historical-role-bridge` | **ESTABLISHED T2**, marqueurs↔rôles du même parent, accords concrets et réalisation injective ; sans surjection sur une histoire étendue. |
| `th.equipped-interior-role-transport` | **ESTABLISHED T2**, retours des rôles intérieurs, position réindexée et lien complet conservés dans la reconstruction reçue. |
| `th.equipped-final-role-full-transport` | **ESTABLISHED T2**, rôle et cinq données choisies conservés ; unicité sur choix fixé. |
| `th.equipped-role-classification-commutes` | **ESTABLISHED T2**, branches conservées et carrés de classification/lecture commutant point par point. |
| `th.separator-relative-role-grammar` | **ESTABLISHED T2**, vide avant choix, choix `Bool` distincts et extension de grammaire ; aucune contradiction avec l'exhaustivité relative. |
| `x.universal-role-exhaustiveness` | **FALSE**, exhaustivité de grammaire déclarée⇒couverture universelle de rôles ajoutés à un autre type. |
| `src.roles-worktree` | **ESTABLISHED**, lot 4, 109 audits et logs build121/vérification124 ; état préparatoire de livraison à dater, HEAD livré distinct. |

## Corrections exactes à appliquer à la carte et à l'exposition

Les corrections suivantes portent sur les données reçues/dérivées, l'adéquation de l'exposition et la chronologie. Elles ne diminuent pas les T2.

1. **`th.rooted-structure.hypotheses`**, remplacer par : « RootedGeneratedHistory et ExactNonClosingRealization ; à chaque position, accord reçu du seul curseur source avec l'adresse canonique. Les accords des états, de la cible et du pas situé sont ensuite dérivés dans la génération canonique enracinée. »

2. **`q.positive-circle.statement`**, dernière phrase : « La génération positive relative à PositiveFormation est réalisée séparément au lot 2, suivie par q.positive-generation. » **`note`** : « Réponse de ce nœud sur les données positives et le pont historique ; la réponse sur la génération relative possède son propre nœud. »

3. **`th.equipped-role.note`** : « Le rôle est unique sur la frontière et la jonction fixées. Son porteur seul ne détermine pas les morphismes riches ; ce nœud porte sur la branche finale. La grammaire complète relative est réalisée au lot 4 dans th.equipped-circular-classification. »

4. **`th.closing-role-choice.note`** : « Aucune unicité de tous les pointages ni occurrence nouvelle engendrée. Ce nœud concerne le rôle sur un choix fixé ; la classification relative des rôles est réalisée séparément au lot 4, et la rigidité générale reste ouverte. »

5. **`th.positive-history-composition.note`** : « L'accord d'indices fait partie du théorème. La propriété universelle des chemins reste ouverte. Le transport des opérations est réalisé au lot 3 pour la formation reconstruite, sans comparaison de formations cibles arbitraires. »

6. **`th.signature-closing-transport.note`** : « Une fibre fermante vide reste sans jonction cible. Ce nœud transporte la clôture et sa frontière équipée ; la classification et le transport des rôles du lot 4 sont établis séparément. Le transport des pôles et de l'obstruction reste ouvert. »

7. **`q.quantity.statement`** : « Quelle signature et quel critère d'équivalence généralisent la quantité structurale déjà constituée par les positions, occurrences, liens, ordre et succession d'un périmètre fixé ? » **`note`** : « Les deux retours du domaine intérieur et les accords structuraux sous transport sont établis. La question restante porte sur une interface générale de quantité et ses comparaisons, au-delà des reconstructions déjà définies. » Le statut `open` reste justifié pour cette généralisation.

8. **`th.numeric-readout.note`** : « History.length compte les pas après leur constitution. La quantité intérieure exacte est déjà portée par les deux retours positions–occurrences et leurs accords structuraux ; la longueur ne constitue ni l'identité ni les relations des occurrences. »

9. **Sources des itérations** : ajouter « À l'itération initiale/du lot N, avant livraison Git, ... » aux assertions « non committées »/« sans commit ». Pour `src.plan`, écrire « Plan local qui était non suivi lors de l'analyse initiale ; désormais suivi à la livraison. Sa référence du 30 septembre et ses interfaces proposées ne certifient pas leur implémentation à cette date. » Conserver les snapshots historiques intacts.

10. **Document `frontiere-sans-jonction-choisie.fr.md`, dernier paragraphe** : « Ce lot concerne la frontière et son enrichissement par un témoin. La génération positive, les transports de fibres et la grammaire relative sont réalisés dans les lots 2, 3 et 4, avec leurs propres scopes. » La limite locale du lot 1 reste vraie ; l'absence présente de ces constructions ne l'est plus.

11. **Commentaire `StrongPerimetralTurning.lean:7031`**, diagnostic uniquement : « Nat enters only here » est littéralement inexact, car `SemanticTrace.Occurrence` utilise `Fin trace.steps.length` à la ligne 4910. Si ce commentaire est retouché dans une autre tâche, préférer « The history-length readout is introduced here after the constitutive boundary; it is not used to construct the canonical occurrence domain. » Cette phase documentaire ne demande aucune mutation de source mathématique ni nouveau run Lean.

12. **Accueil et ordre de présentation** : ouvrir sur le domaine intérieur constitué, ses identités, son exactitude, ses accords structuraux et ses transports. Exposer ensuite la clôture équipée et la continuation hors régime, puis les généralisations ouvertes. Le titre « grammaire relative » est exact mais ne doit pas rendre invisible l'intérieur déjà démontré. Ajouter un statut d'adéquation conceptuelle séparé du tier/review formel : `adequate-relative`, `needs-scope-clarification`, `open-generalization`, ou des équivalents explicites.

Les documents d'origine contiennent déjà plusieurs de ces distinctions correctes, notamment le caractère relationnel de `LocalNode`, les occurrences avant leurs lectures, la quantité non numérique, les quatre statuts constitution/exactitude/étiquetage/admission et la différence entre porteurs et transports riches. La reprise doit les intégrer dans la carte au lieu de présenter l'analyse antérieure comme entièrement fausse.

## Conclusion de phase 1

**ESTABLISHED :** intérieur relationnel constitué et exactement réalisé sur un déploiement fixé, structure d'ordre/adjacence, quantité intérieure avant sa lecture numérique, clôture équipée sans occurrence supplémentaire, transports avec accords explicites, sortie relative du régime historique.

**FALSE :** les 14 implications plus fortes explicitement réfutées par les modèles de la carte ; l'observation présente « plan non suivi » à HEAD ; la lecture ontologique automatique de l'ordre des champs ; l'assimilation d'une équivalence de porteurs à une conservation de constitution.

**GAP :** les généralités universelles laissées ouvertes et l'évaluation finale de la nouvelle carte/document, qui n'ont pas encore été fournis. Aucune révolution de toutes les mathématiques classiques ni suppression de toute donnée reçue n'est démontrée ou requise pour reconnaître le résultat intérieur acquis.
