# Fermeture runtime et distinction gödelienne sous un contrat exact

## Portée et statut

Une production diagonale exécutée unique fournit une ressource positive maître,
puis une histoire H1 partagée par deux sources constitutives distinctes. Le pôle
sémantique lit le type de vérité de la phrase produite ; le pôle syntaxique lit
son type de preuve. Le contrat de futurs et, pour le résultat conditionnel, sa
réalisation exacte sont fixés avant la politique de fermeture. Les deux sources
exécutent la même requête autorisée `close` : leur phase passe d'active à
terminale, tandis que leur pôle, leur histoire, leur provenance positive et leur
readout indexé par le pôle sont conservés.

Une réalisation opérationnelle sans loi d'exactitude du readout conserve les
autorisations, les transitions et les événements. Ses mémoires actives sont
distinctes ; l'exécution de `close` produit ensuite une mémoire terminale
commune et les mêmes événements. Les deux sources constitutives demeurent
distinctes.
Le regroupement ainsi calculé est exposé, sans reconstruire ses runs, ses
événements, ses terminaux ni sa collision, sous l'interface opérationnelle
générique. Une préservation terminale dirigée fournit seulement ses deux
factorisations locales. Leur composition le long de la collision calculée
produit alors `Truth(G) → Proof(G)` sans supposer ni dériver d'égalité entre
`Truth(G)` et `Proof(G)`, sans transport inverse ni `read_exact` global. Seules
les égalités de lecture `read terminal = Truth(G)` et
`read terminal = Proof(G)` fournies par les runs sont utilisées comme
conversions. Cette production ne consomme ni `trueWitness` ni `unprovable`.
Le rejet dirigé les ajoute ensuite depuis le même témoin produit.

Séparément, si une collision des deux terminaux calculés est exigée sous une
réalisation exacte du contrat fixé, les lois d'exécution et de readout imposent
`Truth(G) = Proof(G)`, puis `Truth(G) → Proof(G)`. Ce chemin historique par
égalité reste disponible sans devenir une prémisse du chemin dirigé.

Ces deux témoins certifient par ailleurs un séparateur terminal immédiat. Les
deux runs non vides sur `[close]` calculent d'abord leurs terminaux. La liste vide `[]`
n'exécute ensuite aucune nouvelle fermeture : elle observe les readouts de ces
terminaux déjà produits. Toute `ExactRealization` du contrat doit donc conserver
leur distinction dans ses mémoires projetées. Cette consommation des témoins
appartient au chemin de séparation finie et reste distincte du rejet dirigé.

La collision sous réalisation exacte reste une hypothèse de fermeture, non une
conséquence de Gödel. L'action est autorisée et exécutable indépendamment de
cette hypothèse. Le résultat quantifie sur toute réalisation exacte du contrat
fixé ; il n'affirme ni l'impossibilité de tout regroupement, ni celle de toute
notion de fermeture. Il ne donne aucune borne quantitative de mémoire ou de
coût, et ne porte ni sur le continuum, ni sur AC ou CH. Le mécanisme général
est une obstruction à la fusion exacte de deux observations distinctes ; le
témoin gödelien fixe ici la paire vérité/preuve concernée, l'habitation de la
première et la vacuité de la seconde. Aucune nouveauté mathématique ni aucun
renforcement strict d'un résultat antérieur n'est revendiqué.

L'affirmation `GODEL_OPERATIONAL_RUNTIME_CLOSURE_OBSTRUCTION` conserve son
identifiant. L'adaptateur opérationnel concret, l'exposition générique du
regroupement déjà calculé et le rejet dirigé complètent ses preuves sans
remplacer les chemins historiques. Ces modifications rouvrent ses revues.
Aucun audit indépendant nouveau n'est revendiqué avant lecture d'un rapport
achevé sur cette nouvelle révision. Une traduction anglaise de ce passage est
publiée dans ce lot et demeure elle aussi en attente de revue.

## H1 positif et contrat reçu

La [ressource positive maître](../RelationalPerimeter/Constitution/Godel/PositiveExecutionCore.lean)
reçoit l'histoire de la même `ExecutedGodelProduction` et en extrait les
occurrences ordonnées par un repli structurel positif de ses préfixes. Il ne
relance aucune production diagonale ni l'ancien extracteur dépendant. Le
[module H1](../RelationalPerimeter/Constitution/Godel/OperationalH1.lean)
construit une vraie `History` par trois extensions effectives : production,
certification et continuation. Ses observations d'origine raccordent les deux
premières occurrences aux occurrences exécutées reçues de la ressource maître ;
la troisième est une occurrence nouvellement engendrée. Leur ordre et leurs
distinctions proviennent de la construction de l'histoire. L'égalité éventuelle
de valeurs observées n'identifie aucune occurrence.

Cette construction ne dépend d'aucune présentation gödelienne circulaire ni de son rejet.
Elle ne projette ni `trueWitness` ni `unprovable`. Le type de la production
reçue contient néanmoins les obligations constitutives de la certification
gödelienne : cette dépendance d'interface est distinguée de l'utilisation des
projections négatives dans le runtime.

Une source stocke la ressource maître, H1, son pôle, une histoire opérationnelle
supplémentaire et sa phase. Sa profondeur est une observation calculée de
cette histoire ; elle ne remplace pas les occurrences. Le contexte canonique
construit une fois la ressource maître et H1, puis initialise ses deux sources
avec ces mêmes valeurs. Les continuations postérieures prolongent leur propre
`History` par `History.extend`.

Une famille inductive d'autorisations est partagée à l'identique par le contrat
de futurs et la réalisation opérationnelle. `continue` est autorisé en phase
active ; `close` est autorisé uniquement au H1 actif reçu. Une source terminale
n'admet plus aucune requête. Les transitions totales sur les requêtes non
autorisées restent stables. Les événements donnent la phase et la profondeur
avant et après la requête, sans consulter le pôle.

Le readout constitutif est fixé directement depuis la phrase produite et le pôle.
Le [pont périmétral aval](../RelationalPerimeter/Constitution/Godel/OperationalPerimetralBridge.lean)
consomme la même ressource maître. Il établit un transport exact et exhaustif
entre les occurrences des deux H1, identifie leurs trois rôles et conserve les
deux relations d'ordre immédiat. Ce raccord ne devient pas une prémisse du
noyau de readout ni du rejet runtime.

## Action exécutée et regroupement terminal

La recherche reçoit le contexte H1 et sélectionne `close`. L'autorisation
consomme cette action et fournit un témoin pour chaque source. La décomposition
consomme ces autorisations pour construire deux `ExecutedStep`. Deux
`ExecutedRun` sont ensuite construits à partir de ces étapes ; leurs terminaux
et événements sont ceux des étapes exécutées. Aucune couche ne fournit une
seconde copie arbitraire de ces sorties.

La trace canonique est une `NonemptyRequestTrace` construite avec une tête
`close` et une queue vide. Sa liste calculée est donc `[close]`. La non-vacuité
est issue de cette donnée positive ; elle n'est plus un champ négatif stocké à
côté d'une liste susceptible d'être vide.

La mémoire opérationnelle active conserve la ressource maître, H1, le pôle et
l'histoire reçue. Après `close`, la mémoire `grouped` conserve la ressource
maître, H1 et l'histoire, en oubliant le pôle. Cet oubli intervient seulement
après la transition terminale. Il est justifié par le contrat opérationnel :
aucune continuation n'est admise depuis un terminal, les transitions totales
y sont stables et les événements ne consultent pas le pôle. Les lois de
transport des autorisations, `next_exact` et `event_exact` réalisent ce
contrat sans imposer de readout exact. Cette justification ne prétend pas
établir une `FutureEquivalent` complète, qui inclurait la lecture contestée.

`GodelOperationalRealizationWithoutRead` expose exactement cette séparation.
`godelOperationalGroupingWithoutRead` construit les deux runs sur la trace
canonique, leur collision terminale et leurs événements égaux. Le regroupement
ne vaut donc pas avant l'exécution : les mémoires actives distinguent encore
les pôles. `GodelOperationalRealizationWithoutRead.toOperational` expose les
transitions, événements, autorisations, décisions, projection et lois de cette
réalisation sous `OperationalRealization`, sans transporter son readout réduit
constant. `GodelOperationalGroupingWithoutRead.toExecutedOperationalGrouping`
réutilise directement les deux runs, leurs listes d'événements, leurs terminaux
et leur collision ; seule l'enveloppe générique de la trace non vide est
reconstruite. La réalisation identité demeure exacte pour le contrat fixé ; elle
permet les continuations ouvertes et conserve des terminaux constitutifs distincts
après `close`.

## Exactitude du readout et rejet

`DirectedTerminalReadoutPreservation` reçoit une famille de lecture mémoire,
une factorisation locale du readout gauche vers cette famille et une
factorisation locale de cette famille vers le readout droit. Elle ne reçoit ni
`Truth(G) → Proof(G)`, ni égalité de types, ni loi inverse. Sur
`godelExecutedOperationalGrouping`, `directedReadout` compose ces deux
factorisations le long de l'égalité des mémoires terminales déjà calculée.
`godelComputedGroupingToProducedCompleteness` raccorde les lectures terminales
aux pôles conservés par les deux runs et produit ainsi `Truth(G) → Proof(G)`.
Sa fermeture transitive ne contient ni `trueWitness` ni `unprovable`.
`rejectGodelComputedGroupingToEmpty` applique ensuite le noyau constructif
unidirectionnel à ce transport et aux deux projections du même témoin.

L'instance HA expose séparément la réalisation opérationnelle, le regroupement
calculé, le transport positif conditionnel et son rejet. Elle n'ajoute aucune
hypothèse arithmétique à la production gödelienne déjà exécutée.

Une politique de fermeture sous réalisation exacte reçoit seulement la collision
des deux sorties réduites calculées de `close`. Toutes ses autres couches sont
construites à partir du contexte reçu. La mémoire commune est la sortie gauche ;
la collision raccorde la sortie droite à cette mémoire. La fermeture ne reçoit
ni troisième mémoire, ni égalité de readouts, ni conversion vérité–preuve.

Le noyau utilise `ExecutedRun.terminal_eq_run`, puis le `godelExactRunExact`
direct, prouvé par induction avec `next_exact`. Composées avec la collision,
ces lois produisent l'égalité des projections des terminaux constitutifs. Deux
applications de `read_exact` donnent alors l'égalité de leurs lectures.
La stabilité du pôle et du readout au cours du run ramène cette égalité à
`Truth(G) = Proof(G)`. Aucun fait de vérité ou de non-prouvabilité, aucune
totalisation, aucun rejet circulaire, `event_exact` ou équivalence de tous les
futurs ne fournit ce passage.

`godelTerminalReadExactToEndpointEquality` localise la même frontière pour la
réalisation opérationnelle construite. Dans sa preuve empaquetée, l'adjonction
d'un readout exact est composée avec les deux runs exécutés et leur collision
terminale. Ces runs certifient et conservent la chaîne constitutive effectivement
construite ; ils ne sont pas revendiqués comme les prémisses logiquement
minimales de toute dérivation de l'égalité. Dans cette preuve empaquetée, le
passage critique suit la transition `close`, sa préservation par `next_exact`,
la collision terminale et la préservation des lectures par `read_exact`. Pour
la projection opérationnelle construite, ces étapes ne sont toutefois pas les
prémisses logiquement minimales : l'hypothèse globale `readExact` identifie déjà
les lectures de sources terminales de même mémoire projetée, même lorsque ces
sources sont construites indépendamment des runs. L'ancien raccourci qui
identifiait déjà les projections initiales par leur seule profondeur a été
remplacé, sans alias de compatibilité.

Le transport `Eq.mp` construit ensuite `Truth(G) → Proof(G)`. Cette conversion
est une conséquence typée de l'égalité dérivée, pas un théorème de production
physique d'un code de preuve. Enfin, et seulement alors, `trueWitness` fournit
l'entrée et `unprovable` rejette la preuve ainsi obtenue du même énoncé.
L'équivalence de tous les futurs des terminaux reste une conséquence parallèle
sous réalisation exacte ; elle n'est pas une prémisse du noyau critique.

Le théorème générique `distinct_memory_of_separator` utilise seulement le sens
« même mémoire projetée implique mêmes futurs » de
`equal_memory_same_futures`, puis sa contraposée constructive. Il n'établit pas
la réciproque « mêmes futurs implique même mémoire » et ne caractérise donc pas
la mémoire comme un quotient canonique. `godelTerminalSeparator` applique cette
borne aux deux terminaux effectivement produits par les runs de fermeture. Sa
différence est certifiée par `trueWitness` et `unprovable` du même témoin.

## Localisation fondationnelle exacte

Le témoin gödelien fixe déjà l'incompatibilité entre l'habitation de
`Truth(G)` et la vacuité de `Proof(G)`. L'exécution de `close` ne crée donc pas
cette incompatibilité. Son rôle propre est de construire positivement, dans la
réalisation opérationnelle sans exactitude du readout, la mémoire terminale
commune qui n'existait pas entre les mémoires actives distinctes.

Sous une réalisation exacte arbitraire, `next_exact` transporte la collision
supposée des sorties réduites de `close` vers les projections des terminaux
constitutifs calculés, et `read_exact` force alors l'égalité de leurs lectures.
L'exécution produit et localise ainsi la collision terminale étudiée ;
l'obstruction à sa conservation exacte provient des readouts gödeliens
incompatibles que le contrat exige de préserver.

La frontière démontrée ne constitue pas un principe général suffisant pour
toute constitution relationnelle. Elle porte sur le runtime gödelien construit
et sur son contrat fixé. Chacune de ses deux possibilités positives est
réalisée : le regroupement terminal sous le contrat opérationnel sans readout
exact, et la réalisation exacte qui conserve des terminaux constitutifs distincts.
L'ajout à une réalisation exacte de l'hypothèse identifiant ses deux sorties
terminales calculées est rejeté.

La conclusion exacte est donc :

> **Pour le runtime gödelien construit, `close` produit une collision
> opérationnelle terminale sous une réalisation qui préserve autorisations,
> transitions et événements sans préserver le readout. Pour toute réalisation
> exacte du contrat fixé, le séparateur vide certifié par les témoins impose
> déjà la distinction des mémoires projetées de ces terminaux. De façon
> complémentaire, la collision opérationnelle calculée et une préservation
> dirigée produisent `Truth(G) → Proof(G)` avant toute consommation des témoins,
> puis leur incompatibilité produit `Empty`. Le rejet historique compose
> séparément `next_exact`, la
> collision terminale supposée et `read_exact` pour imposer
> `Truth(G) = Proof(G)`, puis la
> vérité et la non-prouvabilité du même énoncé produisent `Empty`. L'exécution
> construit et localise la collision ; elle ne crée pas l'incompatibilité
> gödelienne qui la rend impossible sous exactitude.**

## Dépendances et contrôles

La formation conserve l'exécution, la ressource maître et H1 dans les types,
ainsi que les données reçues stockées par les sources. L'exécution consomme
successivement recherche, autorisations, étapes, runs et terminaux calculés.
La preuve dirigée consomme le regroupement calculé et deux factorisations
locales ; le rejet ajoute les deux faits gödeliens. La preuve historique
consomme collision et exactitude de transition/readout. Le transport opérationnel oublie le pôle
seulement au terminal sous son contrat sans lecture exacte ; le pont historique
conserve séparément l'identité des occurrences et leur provenance.

Les modules génériques [Execution](../RelationalPerimeter/Constitution/Continuation/Execution.lean)
et [CommonMemoryGrouping](../RelationalPerimeter/Constitution/Continuation/CommonMemoryGrouping.lean)
fournissent les runs et le regroupement sous réalisation complète sans connaître
Gödel. Le [runtime gödelien](../RelationalPerimeter/Constitution/Godel/OperationalClosure.lean)
expose le noyau direct, la conversion produite et les rejets. L'[instance HA](../RelationalPerimeter/Instances/HeytingArithmetic/OperationalClosure.lean)
ferme cette chaîne sur la production arithmétique existante, sans recevoir de
nouvelle hypothèse abstraite pour une donnée déjà construite dans le dépôt.

Le [contrôle de dépendances](../Tests/GodelOperationalClosureDependencies.lean)
parcourt explicitement `ConstantInfo.type` et `ConstantInfo.value?` à chaque
constante rencontrée. Il examine les types et les corps transitifs des racines
positives, rapporte à part les dépendances de l'interface gödelienne reçue,
interdit les projections négatives avant le rejet, vérifie les passages
exécutés requis et contrôle les schémas des sources, événements et traces.
Les régressions positives et les fixtures négatives vérifient des clients
précis de ces interfaces. Ces contrôles mécaniques ne certifient ni le sens
du texte, ni un audit indépendant, ni l'originalité du résultat.

Le résultat antérieur par totalisation est conservé. Aucun théorème ne compare
ses prémisses avec celles de la collision runtime ; ce raccord expose une
autre chaîne conditionnelle sous un contrat de futurs explicite.
