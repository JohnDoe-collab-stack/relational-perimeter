# Plan de chantier — construire les réels depuis le runtime relationnel

## Statut du document

Ce fichier est un document de chantier temporaire. Il ne constitue ni une
affirmation scientifique, ni une modification de la portée des affirmations
enregistrées, ni une preuve d'identification avec les réels usuels. Il devra
être retiré avant une intégration finale dans `main`, après transfert des
résultats établis vers les passages canoniques et le registre.

Point de départ contrôlé : branche `work/runtime-reals-finalization`, commit
`b0870530d79c7cbe80da97cfb4cefb123331cc96`. Le code scientifique auquel les
revues actuelles sont attachées demeure le commit d'évidence
`ffeae501f4425e80705a1b23903dadaf3a3b7937`.

## Cible générale

La cible n'est pas d'enrichir un réel extensif déjà donné. Elle est de
construire, à partir des relations primitives et des exécutions du runtime, une
structure réelle dont la présentation numérique soit un readout aval.

L'ordre constitutif à préserver est :

```text
relations et contextes reçus
  -> sous-exécutions réellement produites
  -> action arithmétique relationnelle
  -> ressource et mémoire suivantes
  -> futurs finis sous contrat
  -> équivalence comportementale
  -> readout dyadique
  -> correspondance avec une présentation extensive
```

Le premier lot implémentable ne vise pas immédiatement tout le corps réel. Il
doit fermer, sans inversion de primitives, la chaîne suivante :

```text
deux comportements réels exécutables
  -> runtime composite d'addition
  -> réel somme exécutable
  -> lois additives à équivalence comportementale près
  -> théorème de readout de la somme
```

Dans ce premier cycle, les deux opérandes vivent sur la même
`CircularPresentation P` et la même `baseDepth`. Le transport entre périmètres,
les opérations multiplicatives, l'ordre et la complétude interne restent hors
portée jusqu'à fermeture de cette chaîne additive.

## Cible terminale : correspondance avec les réels usuels

Le chantier complet vise une correspondance de structures à leurs équivalences
comportementales déclarées, pas une simple fonction de lecture numérique ni
une isomorphie des histoires riches. Il devra construire deux applications :

```text
toExtensive
  : réel relationnel -> présentation extensive d'un réel

fromExtensive
  : présentation extensive d'un réel -> réel relationnel
```

La première est un readout : elle exécute les demandes de précision et projette
leurs réponses. La seconde est une réalisation : elle reçoit une présentation
et construit le runtime qui l'exécute. Elles devront satisfaire deux lois
positives, sans quotient et sans égalité des histoires :

```text
fromExtensive (toExtensive relational)
  ≈runtime relational

toExtensive (fromExtensive extensive)
  ≈extensive extensive
```

`≈runtime` compare les comportements et futurs de précision ; il n'identifie
ni les occurrences, ni les environnements, ni les journaux. `≈extensive`
compare les présentations par leurs approximations cohérentes, pas par égalité
de leurs fonctions brutes.

La correspondance structurelle effective visée est donc comportementale et
numérique, pour la classe effective explicitement définie, non une égalité ou
une isomorphie des familles riches. Le readout extensif reste aval et appauvri :
ses allers-retours ne conservent ni ne récupèrent par ce transport les histoires,
les occurrences ou la donnée positive des témoins de Cauchy. Les constructions
relationnelles primitives et leurs garanties propres restent distinctes de
ce qui est conservé par cette projection.

Ces deux allers-retours existent déjà à un niveau numérique pour
`RuntimeReal`, `EffectiveDyadicPresentation` et `EffectiveCauchyReal.Carrier`.
Les transports individuels déjà fermés couvrent aussi l'addition, l'opposé,
la multiplication, l'inverse sous apartness, l'ordre et l'apartness, ainsi que
leurs raccords carrier, dans leurs portées respectives. Le lot de transport
des familles et de leurs limites est implémenté ci-dessous dans sa portée
comportementale/numérique. Le paquet de la gate 6 agrège ces transports ;
son premier raccord natif avait un défaut constitutif. La correction riche
ci-dessous est implémentée et passe les contrôles locaux, puis revient en
revue primaire avant tout verdict de clôture. Voir la section
« Correspondance structurelle effective comportementale — gate 6 ».
La gate distincte de couverture des réels usuels reste ouverte.

### Critère exact de réussite

La correspondance finale ne pourra être déclarée obtenue que si les deux sens
préservent et reflètent, à leurs équivalences respectives :

- les constantes dyadiques, puis `0` et `1` ;
- l'addition, l'opposé, la multiplication et l'inverse sous apartness ;
- l'égalité réelle comportementale ;
- l'apartness et l'ordre ;
- les lois de corps ordonné ;
- la densité des dyadiques et la propriété archimédienne ;
- les familles de Cauchy internes, leurs limites produites et leur unicité ;
- la complétude pertinente de la construction choisie.

Le théorème final devra donc être un paquet de correspondance contenant les
deux applications, les deux allers-retours et les preuves de transport. Une
collection de théorèmes de readout indépendants ne suffira pas.

### Forme minimale du paquet final

Sans figer prématurément les noms Lean, l'interface terminale devra exposer au
moins les rôles suivants :

```text
CorrespondanceRéelleEffective
  RéelRelationnel
  PrésentationExtensive
  équivRuntime
  équivExtensive
  toExtensive
  fromExtensive
  fromTo                   -- aller-retour côté runtime, à équivRuntime près
  toFrom                   -- aller-retour côté présentation, à équivExtensive près
  préserve_0, préserve_1
  préserve_add, préserve_neg, préserve_mul
  préserve_inv_sous_apartness
  préserve_et_reflète_apartness_et_ordre
  transporte_les_familles_de_Cauchy
  préserve_et_reflète_les_limites_produites
```

Ce schéma est une obligation de contenu, pas une prescription de syntaxe. Un
champ ne pourra être supprimé que si un théorème déjà présent fournit
exactement le même transport dans les deux sens.

Une interface générique portant ces lois ne constituera pas, à elle seule, le
résultat. Le dépôt devra construire une instance concrète pour les runtimes et
présentations retenus, puis dériver le paquet depuis ses réalisations. Les lois
d'aller-retour, de transport et de complétude ne devront pas être réintroduites
comme hypothèses finales de la cible qu'elles sont censées établir.

`fromExtensive` ne recevra pas une valeur numérique opaque. Pour la portée
effective, son entrée devra comprendre le producteur exécutable des
approximations et les témoins constructifs de cohérence ; le runtime construit
devra appeler ce producteur et conserver le pas qui possède sa réponse. Pour
une portée classique plus large, toute donnée non calculable devra être reçue
comme contexte relationnel explicite : elle ne pourra pas être attribuée au
programme seul.

### Cible extensive autorisée

Le dépôt ne doit pas introduire les réels usuels comme primitive amont. La
cible extensive doit d'abord être formulée par des présentations de Cauchy et
leur équivalence positive, déjà amorcées par `EffectiveCauchyReal.Carrier`.
Elle restera sans quotient tant que les règles du dépôt interdisent les
mécanismes quotientant les occurrences.

Pour justifier que cette cible mérite le nom de « réels usuels », il faudra
ensuite prouver qu'elle porte la caractérisation attendue d'un corps ordonné
archimédien complet. Cette caractérisation est une obligation formelle ; le
nom du type ou la présence d'approximations dyadiques ne la remplace pas.

Deux sens de « complétude » doivent être séparés pendant la preuve :

- **complétude de Cauchy effective** : toute famille de Cauchy interne munie de
  son exécution, de son module et de ses témoins produit un runtime limite ;
- **complétude d'ordre ou portée classique** : la propriété de complétude
  retenue pour caractériser les réels usuels s'applique à la classe plus large
  annoncée, avec les données relationnelles positives nécessaires.

La première ne sera pas présentée comme impliquant la seconde tant qu'un
théorème constructif séparé n'aura pas été prouvé sous les hypothèses exactes
du dépôt. Le plan doit donc fermer d'abord les réels relationnels effectifs,
puis franchir une gate explicite de couverture avant toute affirmation sur
les réels usuels sans restriction.

Si une comparaison directe avec un type `ℝ` extérieur est ajoutée plus tard,
elle sera une couche aval séparée. Elle ne pourra ni définir les runtimes, ni
fournir rétroactivement leurs actions, leurs mémoires ou leurs preuves de
cohérence.

### Deux portées à ne pas confondre

Le plan distingue dès maintenant :

1. la correspondance **effective**, pour les présentations munies d'un
   producteur exécutable et de leurs témoins constructifs ;
2. la comparaison avec **tous les réels classiques**, y compris les
   présentations non calculables.

La première est la cible directe du code actuel. La seconde exige une entrée
relationnelle supplémentaire — par exemple une présentation reçue comme
contexte — et ne peut pas être attribuée à un programme fini qui ne la reçoit
pas. Le registre devra donc annoncer séparément la portée effectivement
fermée. Aucun théorème sur les réels effectifs ne sera renommé en théorème sur
tous les réels classiques.

### Matrice de la correspondance terminale

| Structure | Construction relationnelle primitive | Readout extensif aval | Obligation de retour ou de réflexion |
| --- | --- | --- | --- |
| Équivalence réelle | Futurs finis exécutés et témoins de proximité | Équivalence des présentations | Chaque équivalence extensive annoncée induit l'équivalence comportementale, sans égalité d'occurrences |
| Constantes | Runtime constant exécuté depuis un code reçu | Présentation dyadique constante | Le retour produit un comportement équivalent au runtime constant |
| Addition | Deux sous-pas possédés, action unique, cible installée | Addition des approximations | `toExtensive (addRuntime x y) ≈ addExtensive (toExtensive x) (toExtensive y)` et loi réciproque pour `fromExtensive` |
| Opposé, multiplication, inverse | Actions relationnelles avec budgets et témoin d'apartness pour l'inverse | Opérations sur les présentations | Même double compatibilité, sous les domaines de définition exacts |
| Apartness et ordre | Témoins positifs obtenus depuis des exécutions finies | Relations numériques correspondantes | Préservation et réflexion, sans décision globale cachée |
| Famille de Cauchy | Famille interne exécutée, module reçu, regroupement et runtime limite | Famille et limite de présentations | Les deux sens conservent le comportement numérique des termes et comparent les limites à leurs équivalences près ; ils ne récupèrent pas par ce transport les familles riches ni leurs témoins Cauchy |
| Complétude | Producteur de limite et mémoire sous contrat | Énoncé de complétude de la cible extensive | Toute portée extensive revendiquée doit être couverte ; aucun objet absent de l'entrée ne peut être inventé |

Dans toutes les lignes, la colonne « readout extensif » est une projection. Elle
ne peut jamais servir à fabriquer rétroactivement la construction de la colonne
relationnelle ni ses occurrences.

## Base déjà disponible et à ne pas reconstruire

La base actuelle fournit déjà :

- `SignedDyadicCode`, `SameValue`, `Near` et les changements d'échelle
  constructifs ;
- `ExecutedCauchyFamily`, la production des sources, le regroupement historique
  et la limite autoritative ;
- `RuntimeReal`, dont chaque readout est obtenu depuis un pas limite exécuté ;
- `RuntimeReadoutEquivalent` et `LimitFutureEquivalent` ;
- l'aller-retour avec `EffectiveDyadicPresentation` et
  `EffectiveCauchyReal.Carrier` ;
- la séparation entre archive riche, mémoire live, futurs constitutifs et
  équivalence numérique ;
- le raccord gödelien sur le même périmètre et la même base historique.

Ces objets restent valides. Le nouveau chantier doit les étendre par une
couche d'opérations fermée sous composition, pas les remplacer ni les affaiblir.

L'affirmation enregistrée
`RUNTIME_EFFECTIVE_CAUCHY_REAL_CORRESPONDENCE` conserve sa portée actuelle :
correspondance numérique effective, sans opérations de corps, ordre ni
complétude d'ordre. Elle ne sera pas élargie avant les preuves correspondantes.
La correspondance structurelle terminale devra recevoir une affirmation
majeure distincte, ou une révision explicitement rouverte de cette affirmation,
avec passage canonique, portée, références formelles et revues sur le même SHA.

## Décision d'architecture obligatoire

### Voie rejetée

L'addition ne doit pas être définie par :

```text
runtime gauche et runtime droit
  -> extraction de leurs présentations
  -> addition numérique extérieure
  -> presentationToRuntime du résultat
```

Cette voie ferait du readout le constructeur amont de l'opération. Elle
perdrait les deux sous-exécutions et ne prouverait pas que l'action somme les a
effectivement consommées.

Une simple famille dont le `SourceProducer.calculate` appelle deux fonctions
numériques est également insuffisante. Le type actuel de `sourceProgram`
retiendrait le calcul combiné, mais pas nécessairement les deux pas runtime qui
l'ont constitué.

### Voie retenue

Introduire une couche de runtime réel composite, fermée sous les opérations.
Son exécution d'une demande de précision doit :

1. exécuter les deux comportements sources à une précision suffisamment fine ;
2. conserver ces deux pas comme ressources distinctes d'un événement riche ;
3. faire consommer leurs readouts par une unique action dyadique ;
4. produire l'état suivant, l'événement et l'observation depuis le même paquet ;
5. projeter ensuite une mémoire live justifiée par un contrat de futurs ;
6. exposer seulement enfin le code dyadique comme readout.

Trois contrats et une équivalence doivent rester distincts :

- le contrat constitutif riche, qui conserve et peut distinguer les
  sous-exécutions et leurs provenances ;
- le contrat d'archive projeté, qui garde l'index d'archive mais remplace
  explicitement chaque événement riche par son événement live ;
- le contrat live, exécuté sur la seule mémoire projetée par un environnement
  compact ;
- l'équivalence réelle numérique, qui compare les readouts et les futurs
  limites sans identifier les occurrences.

La projection des issues complètes doit être prouvée en deux passages : issue
riche vers issue d'archive projetée, puis réalisation exacte de cette dernière
par l'issue live. La minimalité de mémoire porte uniquement sur le contrat live
— ou, par réalisation, sur le contrat d'archive déjà projeté. Elle ne doit
jamais être reformulée comme une minimalité du contrat riche, car celui-ci
conserve volontairement davantage de provenance. Cette séparation évite de
prétendre que l'égalité du réel somme efface les histoires de ses opérandes.

## Lot 1 — noyau arithmétique dyadique constructif

Créer `RelationalPerimeter/Constitution/Reals/DyadicArithmetic.lean`, important
uniquement `Precision`.

### Données exécutables

Définir positivement, sans entier, rationnel, quotient ou choix classique :

- `SignedDyadicCode.zero` ;
- `SignedDyadicCode.one` ;
- `SignedDyadicCode.add`, après mise à une échelle commune calculée ;
- les témoins exacts de l'échelle effectivement utilisée.

L'échelle commune doit être construite par des additions et des relèvements
explicites. Aucun maximum opaque ni normalisation non traçable ne doit être
introduit si ses témoins ne sont pas conservés.

### Lois de preuve minimales

Prouver avant toute utilisation runtime :

- invariance de `add` sous relèvement d'échelle ;
- congruence de `add` pour `SameValue` ;
- budget d'erreur additif : deux proximités à `Nat.succ precision` produisent
  une proximité de leur somme à `precision` ;
- commutativité, associativité et zéro à `SameValue` près.

Ajouter dans `PrecisionExtension` les seuls combinateurs positifs nécessaires :

- relèvement simultané de la précision ;
- composition de deux extensions de modules ;
- extension de chaque composante vers un seuil combiné.

Les preuves doivent conserver les témoins d'échelle et ne pas réduire les codes
à une valeur entière ou rationnelle extérieure.

## Lot 2 — porteur de runtime réel fermé sous composition

Créer `RelationalPerimeter/Constitution/Reals/HeterogeneousRealRuntime.lean`.
Ce nom rend explicite la combinaison de services dont les types `Memory` et
`Event` peuvent être hétérogènes.

### Interface recherchée

Le porteur doit séparer explicitement :

- le service riche de production, qui possède archives, ressources,
  exécution autoritative et événements riches ;
- l'environnement live fixé, qui ne possède que les opérations exécutables
  lues par la mémoire : lecture, transition et extraction de réponse ;
- la mémoire vivante ;
- la demande finie de précision ;
- le paquet de transition réellement produit ;
- la ressource riche possédée par ce paquet ;
- l'état suivant, l'événement et le readout projetés de ce même paquet ;
- l'accessibilité des mémoires ;
- la cohérence des réponses produites.

L'interface doit permettre à deux instances d'avoir des types de mémoire et
d'événement différents tout en étant combinables. Une occurrence de réel n'est
jamais identifiée à son readout.

Le runtime exécuté doit porter l'environnement live compact et sa mémoire, pas
le service riche. Après effacement des preuves, son environnement calculatoire
ne doit retenir que `read`, `step` et `answer`. En particulier, il ne doit
retenir ni archive initiale, ni producteur riche, ni type de ressource, ni
projection d'archive, ni constructeur d'événement riche. Pour une somme, le
callback live doit capturer les deux environnements live compactés, jamais les
deux services riches. Cette propriété doit être contrôlée dans le code généré,
car le simple fait que `performRuntime` n'appelle qu'un champ ne suffit pas si
son état transporte encore tout le service.

Cette absence de capture riche est une obligation des constructeurs concrets
canoniques, notamment l'adaptateur feuille et `addEnvironment`. La seule forme
du type `LiveEnvironment` garantit ses champs publics, mais ne peut pas exclure
qu'une fonction arbitraire ferme sur des données supplémentaires. Le verdict
de compacité doit donc rester attaché aux constructeurs effectivement compilés
et au contrôle de leurs fermetures ; il ne devient pas un théorème universel
sur tout habitant possible de `Service`.

### Adaptateur autoritatif

Construire un adaptateur depuis `RuntimeCorrespondence.RuntimeReal` vers ce
nouveau porteur. L'adaptateur doit appeler les pas autoritatifs existants et
retenir leur `ExecutedStep`. Il ne doit pas se contenter d'appeler
`RuntimeReal.readout` comme une fonction numérique opaque.

Les deux côtés de cet adaptateur ont des charges différentes. Le service riche
peut conserver le `RuntimeReal`, son archive accessible et l'`ExecutedStep`
produit. Son environnement live ne doit pas capturer ce `RuntimeReal` : il doit
être construit depuis l'environnement exécutable commun formé exactement du
`SourceProducer` et du module. Sa transition live lit cet environnement et la
`ReducedState`. L'égalité avec le pas autoritatif est ensuite un théorème de
projection ; elle n'autorise pas le runtime live à rappeler l'archive riche.

Les égalités suivantes devront être dérivées :

- le pas adapté est le pas autoritatif réellement exécuté ;
- son observation est le readout de la réponse possédée par ce pas ;
- sa cohérence consomme la loi de la famille exécutée ;
- son identité d'occurrence et sa provenance restent disponibles dans la
  ressource riche.

### Constantes du premier cycle

Les comportements `zero` et `one` peuvent réutiliser les runtimes constants
autoritativement exécutés à partir de leurs codes générateurs. Cette
construction est admissible parce que le code dyadique est ici le contexte
reçu qui définit la constante ; il n'est pas extrait du readout d'un réel déjà
constitué pour reconstruire ensuite son runtime. L'adaptateur doit néanmoins
retenir le pas exécuté et prouver que l'observation vient de sa réponse.

### Mémoire exacte

Reprendre la discipline déjà établie pour SAT et `CommonRealRuntime` :

- une archive riche conserve les ressources et provenances nécessaires à la
  preuve constitutive ;
- un événement riche possède l'archive courante et le paquet exact réellement
  produit ; il ne se réduit pas à l'issue live de ce paquet ;
- à environnement fixé, la mémoire live contient exactement les données
  nécessaires aux lectures, transitions et futurs du contrat live complet ;
  un champ tel que `last` peut être lu par `read` sans être lu par une
  transition donnée ;
- l'environnement live contient strictement les fonctions que cette mémoire
  requiert pour lire, avancer et répondre ;
- la projection riche–live est prouvée transition par transition ;
- la projection est aussi prouvée sur chaque trace finie complète, sans
  réexécuter le producteur riche à côté du runtime live ;
- à environnement fixé, l'égalité de la mémoire live est caractérisée par les
  futurs complets de son contrat ;
- cette minimalité ne devient ni un nombre minimal de bits, ni une égalité des
  environnements, ni une équivalence numérique des réels.

Le contrat riche doit rester assez discriminant pour ne pas effacer les deux
opérandes d'une opération lorsque leur somme numérique coïncide. L'événement
riche de l'addition doit donc posséder l'archive d'entrée, la précision et le
paquet de production exact contenant les deux sous-pas et l'action. Son
événement live distinct peut oublier cette provenance, mais seulement par la
projection déclarée. Aucun transport inverse de l'événement live vers
l'événement riche ne doit être disponible. À l'inverse, l'égalité de deux
événements riches d'addition doit entraîner l'égalité de leurs archives
d'entrée par projection de leur champ d'archive : le contrat riche reste donc
effectivement discriminant, et pas seulement plus volumineux.

## Lot 3 — addition relationnelle exécutée

Créer `RelationalPerimeter/Constitution/Reals/RelationalRealAddition.lean`.

### Formation

Une addition est indexée par :

- deux comportements réels déjà constitués ;
- leurs environnements et mémoires initiales ;
- la précision demandée ;
- le décalage de précision nécessaire au budget d'erreur ;
- les deux sous-pas exécutés ;
- l'action qui consomme exactement leurs réponses.

La cible somme ne doit jamais être un champ reçu de la requête.

### Exécution

Pour une demande `precision`, le programme doit :

```text
demander Nat.succ precision au réel gauche
  + demander Nat.succ precision au réel droit
  -> produire deux pas distincts
  -> extraire les deux ressources possédées
  -> exécuter une seule action SignedDyadicCode.add
  -> installer le résultat dans la mémoire suivante
  -> lire ce résultat depuis l'action installée
```

Le code généré devra montrer une application de chaque producteur source et une
application de l'action d'addition par transition, sans second calcul de la
cible au moment du readout.

### Preuve

La preuve de cohérence de la somme doit consommer :

- la cohérence du comportement gauche à la précision successeur ;
- la cohérence du comportement droit à la précision successeur ;
- le lemme dyadique de budget d'erreur additif ;
- les réponses appartenant aux sous-pas retenus par l'action.

Elle ne doit pas appeler séparément les fonctions de présentation des deux
réels pour reconstruire des codes équivalents.

### Transport

Le paquet riche conserve :

- les deux occurrences sources distinguées par leurs rôles gauche/droite ;
- les deux sous-pas et leurs provenances ;
- leur ordre gauche/droite ;
- l'action somme unique ;
- la cible installée.

Le passage au readout oublie ces données seulement au niveau de l'équivalence
numérique déclarée. Il ne fournit aucune réciproque reconstruisant les
occurrences depuis la somme.

Lorsque les deux opérandes ont la même valeur ou même le même comportement,
leur distinction est celle de deux rôles possédés et de deux applications
exécutées dans le paquet, pas une revendication d'inégalité entre leurs valeurs
Lean sous-jacentes. L'égalité éventuelle des ressources ne contracte ni les
deux positions ni leur consommation par l'action.

## Lot 4 — équivalence réelle et lois additives

Définir une équivalence positive entre deux comportements réels composites :

- par proximité de leurs réponses au-delà de seuils exécutables ;
- avec réflexivité, symétrie et transitivité constructives ;
- avec une contrepartie sur toutes les traces finies du contrat numérique ;
- sans quotient et sans égalité des environnements ou des occurrences.

Prouver ensuite :

- congruence de l'addition dans les deux arguments ;
- équivalence de `zero + x` et `x` ;
- équivalence de `x + zero` et `x` ;
- commutativité ;
- associativité.

Ces lois portent sur l'équivalence comportementale. Elles ne doivent pas être
annoncées comme égalités des runtimes riches.

## Lot 5 — théorème de readout, seulement après la construction

Après que l'addition runtime existe et s'exécute, prouver :

```text
readout (addRuntime left right) precision
  SameValue
SignedDyadicCode.add
  (readout left (Nat.succ precision))
  (readout right (Nat.succ precision))
```

Construire ensuite l'addition correspondante sur
`EffectiveDyadicPresentation` et `EffectiveCauchyReal.Carrier`, puis établir :

- préservation du readout par l'addition runtime ;
- réflexion de l'équivalence numérique ;
- compatibilité des allers-retours existants avec l'addition.

La définition du runtime somme ne doit dépendre d'aucun de ces théorèmes aval.

## Matrice de dépendance du premier résultat

| Passage | Indexe les types | Construit les données | Consommé par la preuve | Conservé ou oublié |
| --- | --- | --- | --- | --- |
| Opérandes | Deux comportements et leurs occurrences | Deux sous-pas exécutés | Cohérences gauche et droite | Archive courante et paquet exact conservés dans l'événement riche ; seules leurs projections entrent dans l'événement live |
| Action | Précision et réponses possédées | Code somme unique | Exactitude de chaque sous-pas | Action conservée dans la transition |
| Mémoire | Environnement live compact fixé et état accessible | État suivant installé | Projection vers le contrat d'archive projeté, puis réalisation live | Provenance oubliée seulement sous le contrat live ; service riche absent du runtime exécuté |
| Équivalence | Seuils de réponse | Témoins `Near` | Futurs numériques exécutés | N'identifie ni mémoire riche ni occurrence |
| Readout | Pas somme retenu | Observation aval | Exactitude de l'action | Oublie l'histoire, pas la constitution de la preuve |

## Tests positifs obligatoires

Créer des tests séparés pour :

- exactitude de `zero`, `one` et `add` aux échelles différentes ;
- budget `Near` de l'addition ;
- présence des deux sous-pas dans l'événement riche ;
- identité entre cible de l'action, cible installée et readout ;
- une seule exécution de chaque opérande par pas somme ;
- cohérence de la somme à plusieurs précisions ;
- congruence et lois additives à équivalence près ;
- correspondance du readout après construction ;
- conservation de deux occurrences de rôles distincts et de deux applications
  exécutées donnant éventuellement le même readout, sans exiger l'inégalité de
  leurs valeurs Lean.

## Fixtures négatives obligatoires

Ajouter des fixtures `.lean.fail` empêchant au moins :

- un code somme fourni directement dans la requête ;
- une présentation numérique utilisée comme substitut du runtime somme ;
- un simple `SameValue` utilisé pour fabriquer une provenance d'exécution ;
- un readout recalculé indépendamment de l'action retenue ;
- le pas gauche utilisé à la place du pas droit ;
- deux readouts égaux utilisés pour identifier les occurrences ;
- une archive riche utilisée directement comme mémoire live sans projection ;
- un service riche utilisé directement comme environnement du runtime live ;
- un événement live utilisé comme événement riche sans reconstruction
  explicitement reçue ;
- un environnement caché dans une prétendue mémoire minimale ;
- une loi additive déclarée comme égalité des runtimes riches.

Chaque fixture doit échouer au site prévu avec le diagnostic enregistré, pas
pour une erreur étrangère.

## Fichiers prévus pour le premier cycle

```text
RelationalPerimeter/Constitution/Reals/DyadicArithmetic.lean
RelationalPerimeter/Constitution/Reals/HeterogeneousRealRuntime.lean
RelationalPerimeter/Constitution/Reals/RelationalRealAddition.lean
Tests/RelationalRealArithmetic.lean
Tests/RelationalRealRuntime.lean
Tests/ExpectedFailure/*.lean.fail
```

Les imports publics, audits, manifestes de fixtures, documents canoniques et
registre ne seront mis à jour qu'après fermeture des obligations formelles du
lot. Chaque nouveau fichier Lean portera exactement un bloc `AXIOM_AUDIT` final.

## Ordre d'implémentation et gates

1. Geler un inventaire des déclarations et garanties actuelles.
2. Implémenter et tester le noyau dyadique seul.
3. Vérifier le budget d'erreur avant toute construction de runtime.
4. Implémenter l'interface composite et l'adaptateur autoritatif.
5. Prouver le contrat riche–live et la minimalité à environnement fixé.
6. Implémenter le runtime d'addition et ses tests causaux.
7. Inspecter le code généré pour les applications effectives et le partage.
8. Construire l'équivalence et les lois additives.
9. Ajouter seulement alors les théorèmes de readout et de correspondance.
10. Relire séparément les futurs textes français et anglais.
11. Créer un commit d'évidence exact, puis mettre à jour le registre et les
    revues sur ce SHA.
12. Lancer les gates complètes ; ne demander un audit indépendant que sur un
    SHA poussé et après autorisation humaine.

À chaque étape Lean : aucun `axiom`, `sorry`, `noncomputable`, `Classical`,
`propext`, quotient, `native_decide`, `unsafe` ou construction propositionnelle
masquant des données exécutables.

## Critères de fermeture du premier cycle

Le lot « addition » n'est terminé que si :

- l'opération est produite par un runtime composite, pas emballée depuis un
  readout ;
- les deux sous-exécutions sont possédées et consommées par l'action ;
- la cible installée et le readout proviennent du même paquet ;
- l'archive riche et la mémoire live sont distinctes et exactement raccordées ;
- l'addition est cohérente et congruente à l'équivalence réelle près ;
- les lois de monoïde commutatif prévues sont prouvées à cette équivalence près ;
- le théorème numérique est aval de la construction ;
- les tests positifs, fixtures négatives, audits d'axiomes et contrôles de code
  généré passent ;
- aucun énoncé existant n'a été affaibli et aucun audit historique n'a été
  réétiqueté.

## Lots ultérieurs, hors du premier cycle

### Lot suivant autorisé — opposé et groupe additif

Obligations du lot (distinctes d'un verdict de réussite) :

- échanger positivement les deux composantes signées dyadiques, sans perte de
  précision, puis prouver congruence, involution et annulation additive ;
- produire exactement un pas source à la précision reçue, depuis son archive
  courante ; une action constitutive unaire consomme ce pas possédé et installe
  sa propre cible, sans passer par une présentation ou un carrier ;
- poursuivre le journal arithmétique courant et retenir chronologiquement le
  paquet exact ; l'événement riche possède l'archive d'entrée et le paquet ;
- projeter vers mémoire source live + dernière cible ; la fermeture live de
  `negEnvironment` ne capture que l'environnement live compact du source ;
- conserver les trois contrats antérieurs ; caractériser seulement la mémoire
  live à environnement fixé, jamais les archives riches ou un coût physique ;
- fermer le même arbre de réels sous l'opposé, puis ses lois de groupe additif
  à `Equivalent` et `NumericalFutureEquivalent` près, sans égalité d'occurrences ;
- établir seulement ensuite les transports présentation/carrier, et exécuter
  tests, fixtures à diagnostic exact, audits et contrôle codegen sensible aux
  répétitions, aux archives/journaux réinitialisés et aux captures riches.

État obtenu sur l'arbre de chantier : `RelationalRealNegation` réalise le
service unaire ; `Real.neg` ferme le même arbre sous l'opposé ;
`additiveGroupLaws` et `additiveGroupFutureLaws` fournissent les lois aux deux
équivalences annoncées. Les transports de l'opposé vers les présentations et
carriers sont aval. Build, audit exhaustif, tests, 75 fixtures à diagnostics
exacts, frontières d'import, stratification et sept contrôles codegen passent.
Le contrôle unaire rejette aussi les mutations de réinitialisation d'archive,
de journal et de capture du service riche. Son contrôle de fermeture porte sur
la forme concrète du C épinglé, pas sur toutes les fonctions possibles.
La validation documentaire reste ouverte : `--static` et `--lean` s'arrêtent
sur `STALE_SOURCE: GODEL_RELATIONAL_SEQUENTIAL_COMPLETENESS`. Cela n'autorise
ni rafraîchissement du registre ni réétiquetage des revues. Ce résultat de
chantier n'annonce ni égalité des occurrences ni corps ordonné ni réels usuels.

### Lot multiplication — obligations et résultat sur l'arbre de chantier

Chaque transition doit produire deux sondages à précision 0 depuis les archives
courantes. Pour un sondage `s`, `B(s) = s.positive + s.negative + 1` est une
borne entière de valeur signée, justifiée à échelle commune par `Near 0`.
Elle ne borne pas `positive + negative` des réponses fines non normalisées.

Pour une précision demandée `p`, le raffinement gauche doit partir du successeur
exact du sondage gauche et demander `p + 1 + B(sondage droit)` ; le raffinement
droit fait symétriquement `p + 1 + B(sondage gauche)`. L'inégalité constructive
`B ≤ 2^B` permet d'absorber chaque amplitude ; les deux erreurs à `p + 1`
sont composées à `p`. Les sondages et les raffinements doivent rester des
objets distincts du paquet riche, avec leurs archives successives exactes.
Le budget est un calcul fini explicite, effectivement consommé par les deux
requêtes de raffinement et inscrit dans leurs types ; il n'exige pas une copie
redondante dans l'archive. Une action unique consomme les deux raffinements.

Obligations de fermeture : bornes signées et lemme d'erreur formels ; journal
courant, cible installée et paquet retenu ; trois contrats et projection des
traces ; environnement live compact ; composition et cohérence ; congruence et
lois multiplicatives aux deux équivalences ; transports présentation/carrier
aval ; tests, fixtures exactes et codegen sensible aux réinitialisations,
sondages ignorés, précisions erronées, doublons et captures riches. Rien de
cette liste n'est acquis par sa seule inscription ici. Ordre, apartness,
inverse multiplicatif et nouvelles limites restent exclus du lot.

Résultat formel obtenu : le même `Real` possède maintenant un constructeur
`mul`, dont l'environnement est `mulEnvironment`, construit avant tout
readout multiplicatif. `produceMultiplication` produit les deux sondages
depuis les archives entrantes, calcule une seule fois `productBudget`, produit
les deux raffinements depuis les successeurs exacts des sondages, puis exécute
une seule action arithmétique. `MultiplicationProduction` possède ces quatre
pas et l'action ; les types des raffinements inscrivent directement le budget
issu des deux pas possédés. `multiplicationNext` conserve les successeurs des
raffinements, le journal complété, le paquet ajouté chronologiquement et la
cible lue dans l'action stockée. Ni cette installation ni les observateurs ne
reproduisent les opérandes ou la cible.

| Obligation | Déclaration qui la ferme | Test consommateur |
| --- | --- | --- |
| Amplitude signée, pas taille des composantes fines | `Amplitude.fromProbe`, `signedCrossProductBound` | `cancellationAmplitude`, `fineComponentsNotBoundedByAmplitude` |
| Budget croisé suffisant et erreur du produit | `nat_le_powerOfTwo`, `productToleranceBudget`, `Near.mulRight`, `Near.mul` | `crossBudget`, `nonzeroProductError` |
| Sondages puis raffinements réellement produits | `MultiplicationProduction`, `produceMultiplication` | `currentProbes`, `exactProbeSuccessors`, `twoApplicationsPerRole` |
| Action, journal, cible installée et réutilisée | `multiplicationProgram`, `multiplicationPacketSameTarget`, `multiplicationNext` | `actionConsumesOwnedRefinements`, `installedSameTarget`, `journalContinues`, `retainedChronologically` |
| Projection riche/live et mémoire du seul contrat live fixé | `multiplicationNextProjection`, `multiplicationEventProjection`, `mulEnvironment` | `projectedFutures`, `fixedEnvironmentMinimality` |
| Événement riche discriminant | `multiplicationRichEventReflectsArchive` | `richEventOwnsArchive`, `richEventsDiscriminateHistory` |
| Composition et cohérence depuis toute archive | `Real.mul`, `currentReadout`, `multiplicationCoherent` | `currentReply`, `coherence`, `valueNineSixteenths` |
| Congruence, commutativité, associativité, unités, zéro, distributivité, opposé | `multiplicativeLaws`, `multiplicativeFutureLaws` | `lawPackage`, `futureLawPackage`, `congruence`, `associativity`, `distributivity`, `pairedCurrentFutures` |
| Présentation et carrier seulement aval | `toPresentation_mul`, `toCarrier_mul`, `realization_mul`, `realization_carrier_mul` | les quatre tests de transport/réalisation multiplicatifs |

Les tests de cette table appartiennent à `Tests.RelationalRealMultiplication`.
Les lemmes de bornes et de budget se trouvent dans `DyadicMultiplication`,
avec des audits individuels. Les lois numériques supplémentaires sont dans
`RelationalRealMultiplicativeLaws`. Les seuils de congruence prennent en compte
les amplitudes pertinentes ; `associativityPrecisions` et
`distributivityPrecisions` énumèrent chaque besoin de précision. Leurs sommes
finies sont munies de témoins `PrecisionMember.extension` effectivement
consommés par les preuves. Ce sont des seuils de comparaison de réponses
produites, pas une définition extensive réimportée dans le runtime.

La mémoire live multiplicative contient seulement les deux mémoires enfant
et la dernière cible, toutes lues par son contrat. La fermeture exécutable
contient les deux environnements live compacts, pas les services ou archives
riches. Deux opérandes aliasés gardent deux rôles, deux sondages et deux
raffinements : quatre applications enfant au total. Les lois portent uniquement
sur `Equivalent` et `NumericalFutureEquivalent`, jamais sur l'égalité de ces
occurrences. Les trois contrats antérieurs restent séparés ; aucune minimalité
riche ou physique n'est affirmée.

Vérifications locales : build de 370 jobs, audit exhaustif de 34248 constantes
sur 367 modules (`generatedExceptions=662`, `writtenExceptions=0`), 368 fichiers
Lean avec bloc terminal unique et aucun mécanisme interdit, 83 fixtures à
diagnostics et sites exacts, frontières d'import et inventaire de stratification
de 311 modules de production. Les huit contrôles codegen passent. Le contrôle
multiplicatif vérifie les archives et journaux courants, les successeurs exacts
des sondages, les origines croisées des précisions, leur calcul numérique, la
multiplicité même sous aliasing, le partage de la cible et la capture compacte.
Il rejette notamment les mutations de remise à zéro, sondage ignoré, amplitude
croisée inversée, bit de précision ou marge supprimés, recomputation de cible
dans les observateurs/installateur et capture du service riche. Son périmètre
est celui des routes C épinglées et des frontières de callbacks explicites ;
il ne constitue pas un théorème de coût ni un contrôle physique de heap.
L'autotest supplémentaire des gates de fixtures passe également ses 20 cas
Bash/PowerShell : deux baselines de 83 fixtures et 18 mutations, rejouées sans
rebuild concurrent des artefacts partagés.

La gate documentaire reste ouverte : `check-scientific-docs.py --self-test`
passe, mais `--static`, `--lean`, `verify.ps1` et `verify.sh` s'arrêtent sur
`STALE_SOURCE: GODEL_RELATIONAL_SEQUENTIAL_COMPLETENESS`, déjà présent avant
ce lot. Aucun registre, passage canonique/protégé, figure ou statut de revue
n'a été modifié pour contourner cet arrêt. Le résultat local est une fermeture
multiplicative relationnelle et ses lois numériques, pas un corps ordonné ni
la clôture de la correspondance terminale du plan.

### Lot apartness positive, signe et ordre : résultat de chantier

Le noyau `DyadicOrder` construit un certificat orienté `StrictSeparation p x y`.
À son échelle commune `s = p + e`, sa marge est exactement
`x⁺ + y⁻ + 2^e < y⁺ + x⁻`, où les quatre composantes sont relevées à `s`.
La tolérance signée est donc `2^-p` ; les annulations des codes non normalisés
ne sont jamais remplacées par une comparaison de leurs seules composantes.
`DirectedUpper` est la borne unilatérale correspondante, pas un `Near` global.
`inspectGap` calcule sur ces données finies soit cette marge stricte, soit la
borne unilatérale inverse. `classifyFinite` examine ensuite l'autre direction
si nécessaire. Sa branche `inconclusive` conserve seulement les deux bornes
des deux réponses de cette tentative : elle n'affirme ni égalité réelle, ni
négation d'apartness, ni proximité à toutes précisions.

`RelationalRealOrder.produceComparison` exécute les deux services aux archives
courantes reçues, une fois par rôle, puis classe les codes des deux `Step`
possédés. `ComparisonAttempt` retient ces étapes, le résultat effectivement
classé et `PrecisionExtension (p + 3) response`. `StrictOrder` possède les
archives, les deux étapes et la marge orientée ; `Apartness` est une donnée
positive en `Type` distinguant ses deux directions. Les constructeurs privés
ne sont pas une substitution à cette chaîne : la voie publique productrice
est l'exécution et la classification de ses réponses. L'extraction
`ComparisonAttempt.forward` conserve le certificat produit ; la marge reçue
en argument sert uniquement à éliminer ses autres branches. `Positive` et
`Negative` sont les deux ordres orientés avec un opérande zéro effectivement
exécuté ; `signCurrent` et `sign?` restent des tentatives finies optionnelles.

Les bits de garde ne sont pas une constante présumée suffisante :

- `DirectedUpper.compose` consomme deux tolérances `p+1` pour une tolérance `p`.
- `strengthenSeparation` transporte une marge `p` avec deux `Near (p+2)`
  et produit une marge `p+2`. L'absence de cette dernière donnerait trois
  bornes à `p+2`, composées en une borne inverse à `p`, contradictoire.
- `refineHistorical` repart des successeurs exacts du témoin reçu, demande
  au moins `p+5`, consomme la cohérence des étapes anciennes et nouvelles à
  `p+3`, puis affaiblit à `p+2`. La marge résultante et le budget de réponse
  satisfont de nouveau le contrat, à la nouvelle précision `p+2`.
- `transportOrder` utilise la somme explicite
  `[p+5, left.threshold (p+3), right.threshold (p+3)]`. Il produit une paire
  source aux successeurs exacts et une paire cible aux archives cibles reçues.
  Deux cohérences historiques et deux témoins `Equivalent.near` à `p+3`
  donnent par composition les deux `Near (p+2)` consommés. Le contrat
  `Equivalent` reçu est numérique ; ses callbacks ne sont pas annoncés comme
  des actions constitutives supplémentaires de la comparaison.
- `cotransition` produit exactement trois étapes à `p+5`. La même étape du
  milieu est partagée par les deux comparaisons possibles. Si aucune marge
  `p+2` ne réussissait, quatre bornes à `p+2`, dont les deux cohérences des
  extrémités, composeraient une borne inverse à `p`, contredisant le témoin
  initial. Les deux bits de cette composition sont consommés explicitement.

| Passage | Formation | Exécution | Preuve consommée | Transport / oubli |
| --- | --- | --- | --- | --- |
| Tentative finie | services, archives courantes, précision et budget | deux `perform`, puis classification de leurs codes | exactitude de la classification | les deux rôles et ressources sont retenus, même sous aliasing |
| Ordre / apartness | étapes possédées et marge stricte orientée | extraction du résultat exécuté, sans nouvelle sortie prescrite | élimination des autres branches finies | direction conservée ; aucune identification d'occurrences |
| Raffinement / transport | témoin original retenu et étapes nouvelles exactes | successeurs natifs, paire source et paire cible | cohérence, seuils reçus, compositions et marge | résultat numérique invariant, histoires et événements non égalisés |
| Cotransitivité | témoin original et triple possédé | trois productions, milieu partagé | quatre tolérances et contradiction de la marge | somme positive des deux directions possibles, pas de trichotomie |
| Projection aval | témoin opérationnel complet | aucune reconstruction du runtime depuis une présentation | `currentReadout` sur les étapes reçues, avec références canoniques possibles dans son raccord propositionnel, y compris composite | les occurrences sont oubliées, pas la direction ni la marge |
| Réflexion aval | certificat numérique et archives reçues | nouvelle tentative native et classification effectives | certificat numérique raccordé aux réponses par `currentReadout` | produit de nouvelles occurrences, ne reconstitue pas celles oubliées |

Lois effectivement obtenues : irréflexivité de l'ordre et de l'apartness,
asymétrie, transitivité de l'ordre, symétrie et cotransitivité de l'apartness,
exclusion d'une équivalence numérique, exclusion des deux signes simultanés,
stabilité historique, transport sous `Equivalent` et sous
`NumericalFutureEquivalent`, et renversement de l'ordre par l'opposé exécuté.
Les éliminations vers `Empty` consomment une marge positive et des tolérances
constructives ; elles ne transforment pas l'apartness en négation classique.
`noneOfEquivalent` est seulement le sens « équivalence reçue implique tentative
inconclusive » ; aucune réciproque n'est introduite. Aucune décision totale,
trichotomie globale, compatibilité avec addition/multiplication, inverse ou
loi de corps ordonné n'est revendiquée par ce lot. Les compatibilités d'ordre
avec addition et multiplication restent des obligations du lot de corps
ordonné, non des conséquences des seules lois numériques multiplicatives.

`PresentationOrder` / `PresentationApartness`, puis `CarrierOrder` /
`CarrierApartness`, sont définis après la construction relationnelle. Les
préservations et réflexions portent exactement sur ces certificats finis
à budget explicite. `realizePresentationOrder` et `realizeCarrierOrder`
réalisent aussi les certificats reçus sur des présentations/carriers arbitraires
dans la portée effective antérieure. La réflexion exécute aux archives reçues
et ne permet pas de transformer un readout nu en occurrence historique.

Il n'y a pas de service de comparaison persistant artificiel : le paquet de
tentative est fini, ses futures exécutions sont précisément celles des deux
services natifs, et `continueComparison` les lance sur les deux successeurs
possédés. Le triple et les paquets de transport sont eux aussi des ressources
de preuve exécutées non persistantes. Les trois contrats existants (service
riche, archive projetée, live) restent séparés. La comparaison ne crée donc
ni mémoire `Unit` prétendument minimale ni nouvelle fermeture capturant les
archives riches. Les minimalités existantes restent strictement relatives
au contrat et à l'environnement fixés ; aucune minimalité riche ou physique.

La relecture a aussi corrigé le corps de `leafCoherent`, sans modifier son
type, ses quantifications ou ses seuils : il applique désormais `family.cauchy`
aux deux `source.execution` des `limitProduction` possédées par les étapes
reçues, au lieu de reconstruire des étapes canoniques par `real.readoutsNear`.
Ses consommateurs addition, opposé, multiplication, équivalence et ordre
ont été recompilés. Le contrôle C marque et vérifie séparément les journaux,
requêtes et exécutions source exacts transmis au callback Cauchy ; il interdit
transitivement les routes canoniques dans ce corps. Il ne prétend pas imposer
le corps d'un callback Cauchy générique fourni par un client.

Vérifications du lot : `Tests.RelationalRealOrder` couvre témoins stricts,
archives/journal non vides, rôles aliasés, annulation non normalisée,
raffinements, seuils de transport, cotransitivité, signes, opposé et transports
aval. Neuf fixtures verrouillent les erreurs au site et au diagnostic exacts,
y compris la branche finie inconclusive qui ne peut fournir aucune direction
stricte. Le contrôle codegen épinglé distingue les deux applications aliasées,
le milieu partagé du triple, les archives et successeurs courants, le budget,
la classification des réponses réellement possédées et la cohérence des
sources reçues ; il rejette des mutations de remise à zéro, d'inversion,
de sous-budget et de reconstruction canonique. Ces contrôles bornés ne sont
ni un théorème de coût ni un contrôle physique de mémoire.

Build complet final : 373 jobs ; audit exhaustif `constants=34722 modules=370
generatedExceptions=678 writtenExceptions=0`. Les 371 fichiers Lean possèdent
chacun un bloc terminal unique et leur artefact compilé ; les scans constructif
et architectural ne trouvent aucun mécanisme interdit. Les frontières d'import
(quatre configurations et leurs autotests), la stratification de 313 modules
de production et les neuf contrôles codegen passent. Les 92 fixtures passent
aux diagnostics et sites exacts ; les deux gates Bash/PowerShell passent
aussi leurs 20 cas d'autotest (deux baselines de 92 fixtures et 18 mutations).
Les tests vérifient aussi les trois branches numériques du classifieur fini,
un signe négatif produit aux archives non vides et un transport vers deux
programmes distincts. Le diff-check couvre les fichiers suivis et nouveaux.

`check-scientific-docs.py --self-test` passe ses sept cas. `--static`, `--lean`,
`verify.ps1` et `verify.sh` sous Git Bash s'arrêtent sur le premier défaut
`STALE_SOURCE: GODEL_RELATIONAL_SEQUENTIAL_COMPLETENESS`, déjà constaté avant
ce lot. Le contrôle documentaire n'est donc pas déclaré vert et aucune
empreinte, entrée du registre, cible canonique ou revue n'a été rafraîchie.

### Lot inverse — raccord et fermeture numérique sous apartness exécutée

Le domaine reçu est `Apartness source (zero P baseDepth)`, avec sa direction
et ses étapes possédées. `ReciprocalDomain` calcule `away = accuracy+2` et
reprend comme archive source initiale le successeur exact du `Step` source du
témoin. Pour chaque nouvelle étape courante, `nonzero` transporte explicitement
la marge initiale par la cohérence des étapes source reçues et l'exactitude du
zéro effectivement possédé. Il produit un `NonzeroCode` dans la même direction,
avec soustraction naturelle exacte malgré les annulations et borne
`2^source.scale ≤ magnitude * 2^away`. Le témoin n'est donc pas seulement stocké.

`DyadicReciprocal` construit sa propre division naturelle par soustractions
avec carburant structurel décroissant, dénominateur strictement positif reçu
avant la division et invariant empêchant l'épuisement prématuré. Le paquet
quotient/reste prouve `q*D+reste=N` et `reste<D`. À précision d'arrondi `t`,
`N=2^source.scale * 2^t` et le code produit est `±q/2^t`. Un
`ReciprocalResult` possède cette division, la cible calculée une fois et son
exactitude ; les preuves de cohérence et d'erreur d'unité reçoivent ce paquet,
elles ne relancent pas la division. Les comparaisons naturelles croisées
auxiliaires ne sont pas un carrier rationnel ni une entrée extensive.

Pour une demande `n`, le budget effectivement exécuté est
`sourcePrecision away n = n+2+(away+away)` et `roundingPrecision n = n+2`.
Le lemme `reciprocalNear` consomme les deux bornes non nulles et les deux
paquets de division reçus : deux exposants `away` absorbent l'erreur de la
source, puis les deux arrondis et cette erreur, chacun à `p+2`, sont composés
explicitement à `p`. `reciprocalUnit` ferme seulement l'erreur dyadique locale,
avec amplitude et budget reçus. Ce n'est pas encore une loi d'unité runtime.

`ReciprocalRuntime` exécute la source depuis son archive courante au budget
calculé, construit son certificat non nul depuis le témoin exécuté, puis fait
consommer cet opérande exact par une action réciproque unique. Cette action
produit la division et la cible, consommées par sa préservation. L'état suivant
reprend le successeur source possédé, le journal arithmétique complété, le
paquet ajouté chronologiquement et la même cible stockée. Événement et lecture
projettent ce résultat sans reconstruction. `inverseCoherent` compare les
étapes source et divisions effectivement reçues ; `inverseUniform` dérive
l'invariance historique à précision fixée par l'unicité du quotient et celle
des réponses source, sans hypothèse terminale supplémentaire.

La mémoire live est mémoire source + dernière cible. Sa fermeture est construite
depuis l'environnement source compact, la direction et `away`, tous trois lus
par l'exécution. Aucun témoin ou service riche n'est un paramètre de cette
fermeture live. Le contrôle mutation-sensitive des captures porte sur ces
constructeurs concrets compilés, pas sur tout service externe possible.
La spécification live doit être totale même
hors des images d'archives riches : elle teste `D>0` avant de construire la
division et rend un code de repli sinon. `codeProjection` élimine cette branche
depuis le `NonzeroCode` du `Step` exact ; aucune loi réciproque n'est donnée au
repli et aucune division par zéro n'y est exécutée. Les trois contrats et la
minimalité au seul environnement fixé sont hérités du service commun.

Le raccord dans le même `Real` a exigé une décision explicite d'univers : un
`Service`, dont les types d'archive/mémoire/événement sont des données, appartient
à `Type 1`, alors que l'ancien `Real` appartenait à `Type`. La montée de `Real`
à `Type 1` est explicite. Ses quatre anciens constructeurs sont conservés ;
`Coherent` est déplacé sans modification. Le nouveau `CertifiedService`
possède un service, sa cohérence sur les étapes reçues et l'invariance exacte
des codes à précision fixée depuis toute archive/étape. Le constructeur
`Real.certified` étend uniquement les trois éliminateurs `environment`,
`currentReadout` et `coherent`. Un certificat externe générique reste une
entrée relationnelle reçue, pas une réalisation endogène.

`RelationalRealInverse.inverse` construit concrètement ce certificat depuis
`inverseEnvironment`, `inverseCoherent` et `inverseUniform`. Il ne passe par
aucune présentation, aucun carrier ni pseudo-feuille reconstruite. La
comparaison mécanique des 98 déclarations antérieures d'addition ne trouve
qu'un changement d'en-tête : le sort autorisé de `Real`. Les quatre anciens
constructeurs et le bloc `Coherent` sont textuellement identiques ; les
énoncés et quantifications des anciens théorèmes n'ont pas été retouchés.

Le checkpoint compile les modules Addition, Multiplication, MultiplicativeLaws,
Order, ReciprocalDomain et ReciprocalRuntime (45 jobs), puis le raccord et
`Tests.RelationalRealInverseRaccord` (52 jobs). Ces tests couvrent ancrage exact,
consommation du témoin/opérande, cible partagée, archives et journal non vides,
deux précisions, deux signes, annulations, projection des traces et minimalité
du seul contrat live fixé.

La reprise suivant ce checkpoint ferme les unités runtime, et non le seul
lemme dyadique local. `mul_inverse_step` reçoit un `Step` du produit depuis
une archive arbitraire et l'extension
`p+1+probeAmplitude step.resource.rightProbe.code ≤ response`, sous sa forme
positive `PrecisionExtension`. Il consomme les deux sondages réels du paquet,
le raffinement source gauche et le `sourceStep` possédé par le raffinement
inverse droit. La cohérence source compare ces deux étapes à
`p+1+amplitudeInverse`. L'amplitude inverse, déduite du vrai sondage droit,
absorbe ce premier écart et donne une erreur à `p+1`. L'amplitude source,
déduite du vrai sondage gauche et de la cohérence avec le `sourceStep` droit,
est consommée par `reciprocalUnit` sur le `ReciprocalResult` réellement reçu.
Son arrondi à `response+1+amplitudeSource+2` satisfait le budget requis à
`p+1`. La composition des deux erreurs donne `Near p` au code unité. Aucun
Step, sondage, quotient ou résultat de division n'est reconstruit dans ce
lemme historique.

`mul_inverse` expose l'unité `source * inverse source witness ≈ one` à
`Equivalent` près ; `inverse_mul` en déduit l'autre orientation par la
commutativité déjà prouvée. Leurs versions `mul_inverse_futures` et
`inverse_mul_futures` portent sur les traces numériques finies depuis toutes
archives courantes. Ces équivalences n'identifient ni événements, ni mémoires,
ni occurrences. `witness_independent` dérive l'indépendance de deux témoins
par les deux unités, congruence et associativité multiplicatives : elle ne
refait pas une inversion. `inverse_congr` étend le même argument à deux
sources numériquement équivalentes munies de leurs propres apartness exécutées.
Les deux résultats ont leur contrepartie `NumericalFutureEquivalent`.

Les transports sont introduits seulement après ces lois.
`PresentationDomain P baseDepth source` est une apartness numérique positive
entre la présentation reçue et la présentation du zéro du périmètre fixé.
`realizePresentationDomain` produit des comparaisons natives fraîches sur les
archives reçues ; elle ne restaure pas les occurrences effacées. L'opération
aval `inversePresentation` est alors définie par réalisation du source,
exécution de son inverse relationnel et projection `toPresentation`.
Il n'existe pas d'inverse extensif indépendant utilisé pour fabriquer le
runtime. `toPresentation_inverse` dérive la préservation par `inverse_congr`
et l'aller-retour du source ; `realization_inverse` dérive la réalisation de
cette présentation par l'aller-retour du runtime inverse déjà produit.
`CarrierDomain`, `realizeCarrierDomain`, `inverseCarrier`, `toCarrier_inverse`
et `realization_carrier_inverse` reprennent exactement cette direction via
le carrier effectif. Ces opérations aval restent attachées au périmètre et
à la base reçus ; aucune couverture classique supplémentaire n'est annoncée.

| Obligation | Déclarations de production/preuve | Tests et verrouillages |
| --- | --- | --- |
| Marge du témoin vers chaque étape, direction, successeur exact | `ReciprocalDomain.nonzero`, `sourceSuccessor` | tests de raccord, fixtures direction/archive/ancrage ; contrôle C des deux branches de direction |
| Production unique quotient/reste et cible partagée | `computeReciprocal`, `ReciprocalRuntime.program`, `packetSameTarget` | annulations des deux signes, fixtures code/paquet/action ; mutations de duplication valide et de quotient ignoré |
| Budgets réellement consommés et unités runtime | `mul_inverse_step`, `mul_inverse`, `inverse_mul` | `unitFromCurrentPacket`, `currentProductArchives`, unités positives/négatives ; budgets C numériques et mutations |
| Indépendance du témoin et des encodages numériques | `witness_independent`, `inverse_congr`, versions futurs | deux témoins fraîchement exécutés, source constante non normalisée équivalente ; fixtures interdisant l'égalité des occurrences |
| Archive courante, journal et rétention chronologique | `produce`, `next`, `Production.source_is_produced` | tests de raccord à deux précisions et journal non vide ; mutations archive/journal/certificat reconstruit |
| Contrats séparés, projection et live compact | `codeProjection`, `nextProjection`, `eventProjection`, `inverseEnvironment` | traces projetées, minimalité à environnement fixé, fixtures archive/certificat riche ; captures C compactes et repli sans division |
| Présentation/carrier uniquement aval | `realizePresentationDomain`, `toPresentation_inverse`, `realization_inverse`, analogues carrier | tests de transport et réalisation ; aucun chemin de construction runtime vers ces modules aval |

`Tests.RelationalRealInverse` ajoute trente déclarations auditées au raccord :
unité sur paquet courant après une première multiplication, unités des deux
signes et leurs futurs, nouveau témoin produit depuis un successeur non vide,
indépendance de témoins, encodage avec annulation, deux programmes équivalents,
transports/réalisations et trace numérique à deux précisions depuis les
archives courantes. Quinze fixtures supplémentaires enregistrent les erreurs
de Lean à leurs sites et diagnostics exacts. Elles empêchent notamment code,
marge ou Step nu de remplacer l'apartness, la direction inversée, la remise
à zéro de l'archive, la cible prescrite, le remplacement du paquet/action par
un calcul isolé, les captures riches typées et l'égalité des occurrences.

`check-real-inverse-codegen.py` vérifie la route C épinglée : applications
source/action/division uniques, certificat recevant le Step effectivement
produit, ancrage par les deux successeurs orientés du témoin, budget depuis
`away` et la demande, journal courant, paquet/cible partagés et rétention.
La route live lit la seule mémoire source courante et conserve le successeur
exact ; ses captures sont environnement compact source + direction + `away`.
Le repli teste la magnitude contre zéro avant toute division. Vingt-sept
mutations contrôlent notamment les duplications valides, les sous-budgets,
les remises à zéro, la perte du quotient, la division avant le garde et les
captures riches. Les frontières explicites d'analyse sont l'exécution native
du source et la certification quantitative déjà prouvées dans Lean ; elles
ne deviennent ni un contrôle universel des callbacks externes ni un théorème
de coût ou de mémoire physique.

Vérifications finales de cette fermeture : build complet de 381 jobs ;
`ALL_CONSTANTS_OK constants=35236 modules=378 generatedExceptions=691
writtenExceptions=0`. Les 379 fichiers Lean passent le scan constructif,
les frontières architecturales, le bloc d'audit terminal unique et la présence
des artefacts compilés. Les quatre frontières d'import et leurs quatre
autotests passent ; la stratification couvre 319 modules de production sans
orphelin. Les 107 fixtures passent à leurs diagnostics et sites exacts, sans
erreur supplémentaire. Les dix contrôles codegen passent ; le nouveau contrôle
inverse rejette mécaniquement 27 mutations. Le diff-check couvre aussi les
fichiers nouveaux. L'autotest des deux gates de fixtures passe ses vingt cas :
deux baselines de 107 fixtures et dix-huit refus de mutations Bash/PowerShell,
avec contrôle séparé des statuts de processus et de l'identité des diagnostics.
Les sept autotests documentaires passent ; `--static`,
`--lean`, `verify.ps1` et `verify.sh` sous Git Bash s'arrêtent tous sur le
stale Gödel préexistant ci-dessous, pas sur un succès documentaire supposé.

Cette fermeture numérique de l'inverse ne constitue pas le paquet de corps
ordonné : aucune compatibilité nouvelle entre ordre et multiplication,
densité, nouvelle complétude ou correspondance finale n'est annoncée. Le
blocage documentaire `STALE_SOURCE: GODEL_RELATIONAL_SEQUENTIAL_COMPLETENESS`
reste à rapporter sans modifier le registre ni rafraîchir ses empreintes.

### Compatibilités constructives de corps ordonné — résultat du lot suivant

`DyadicOrderedField` et `RelationalRealOrderedField` ajoutent un paquet de
lois de corps ordonné constructif au niveau `Equivalent`, puis de ses futurs
numériques. Il ne s'agit pas d'une instance de corps total/extensif : les
objets restent des occurrences, l'inverse reste défini seulement sous
`Apartness source zero`, et la monotonie multiplicative reçoit un témoin
`Positive factor`. Une apartness non orientée ne remplace pas ce signe.
Le lot ne construit ni densité, ni propriété archimédienne, ni nouvelle
famille de Cauchy, ni correspondance terminale avec les réels usuels.

Le noyau dyadique conserve exactement la marge stricte sous `SameValue` et
translation, même pour des codes non normalisés. `NonzeroCode.mulPositive`
consomme deux bornes positives quantitatives : à partir des exposants
`κa = left.accuracy + 2` et `κb = right.accuracy + 2`, il donne une
`StrictSeparation (κa + κb + 1) zero (a.mul b)`. Les deux bornes se
multiplient à échelle commune ; le bit supplémentaire rend la marge stricte.
Il n'y a ni test de signe nu utilisé comme preuve d'ordre, ni borne sur la
somme des composantes positive et négative d'un code avec annulation.

`TranslatedOrder` possède le témoin source et une unique `ComparisonAttempt`
exécutant les deux sommes depuis leurs archives reçues. À partir d'une marge
source à `p`, les deux cohérences consomment les Steps source reçus et les
sous-Steps réellement contenus dans les productions de somme ; elles donnent
`Near (p+2)` aux codes source des deux actions. Les sommes répondent à `p+5`,
leurs enfants à `p+6`. `strengthenSeparation` puis la translation dyadique
construisent la séparation des deux sorties réellement produites. Les deux
occurrences du décalage restent deux exécutions ; `currentReadout` n'établit
que l'égalité de leurs codes à la même précision, jamais celle de leurs Steps,
archives ou occurrences. `TranslatedOrder.order` extrait la direction depuis
la classification de cette même tentative ; il ne refait pas un calcul
numérique indépendant. `addOrderRight`, `addOrderLeft` et `reflectAddRight`
ferment translation et réflexion, via des transports dirigés frais pour les
commutativités et annulations nécessaires.

`PositiveProduct` possède séparément les deux témoins positifs, la tentative
zéro/produit exécutée, les deux certificats quantitatifs et la marge finale.
Sa précision de marge est `κa+κb+1`, sa réponse cette précision plus trois.
La production multiplicative native garde ses deux sondages et ses deux
raffinements. `ReciprocalDomain.nonzero` transporte chaque marge positive
reçue vers le raffinement exact possédé par le produit, à la précision calculée
par `productBudget` depuis ses vrais sondages ; ni un Step canonique, ni un
code reconstruit ne le remplace. `mulPositive`, l'exactitude de l'action
produite et l'exactitude du Step zéro donnent la marge de la même tentative.
`PositiveProduct.positive` en extrait son témoin orienté.

`PositiveDifference` construit `0 < b + (-a)` depuis `a < b` par translation
exécutée puis transport `a+(-a) ≈ 0`. `MultipliedOrder` retient dans cet ordre
la différence positive, le produit positif avec le facteur reçu, sa
translation par `a*c`, puis le transport final. La distributivité et les
annulations déjà prouvées à `Equivalent` près donnent
`((b+(-a))*c)+(a*c) ≈ b*c`. Chaque transport d'ordre exécute ses propres Steps
cibles frais. Les entrées natives du transport final sont exactement le
successeur du Step `a*c` possédé par la somme gauche et les successeurs des
Steps `b` et `c` possédés par les raffinements du produit de la somme droite.
`mulOrderRight` et `mulOrderLeft` en déduisent la monotonie sous `Positive`.
`apartAddRight` et `apartMulPositiveRight` conservent les deux orientations
distinctes de l'apartness, sans transformer celle-ci en signe du facteur.

| Passage | Formation et exécution | Preuve consommée | Conservation / oubli |
| --- | --- | --- | --- |
| Translation | Deux archives courantes, deux Steps de somme et leurs actions | Témoin orienté, deux cohérences sur sous-Steps reçus, marge dyadique | Le paquet conserve témoin, tentative, `Near` et marge ; aucune identité des deux décalages |
| Produit positif | Deux témoins positifs, sondages, budgets et raffinements du produit courant | Transport de chaque signe vers son raffinement exact ; multiplication des bornes ; action exacte | Deux certificats restent attachés aux deux rôles, même en cas d'alias |
| Monotonie | Différence, produit, translation et transport réellement produits une fois | Lois relationnelles antérieures à `Equivalent` près ; marges et Steps des paquets reçus | Quatre sous-paquets chronologiques ; successeurs natifs `a*c`, `b`, `c` exacts |
| Paquet de lois | `orderedFieldLaws` et `orderedFieldFutureLaws`, sans hypothèse terminale nouvelle | Groupe additif, anneau multiplicatif, ordre positif, unités sous apartness et compatibilités ci-dessus | Futurs strictement numériques ; ni événements ni occurrences inter-environnements identifiés |

Il n'y a pas de nouveau service persistant ou de nouvelle fermeture live.
Les paquets sont des productions finies de preuve-exécution qui utilisent les
runtimes arithmétiques natifs ; les trois contrats et l'équivalence numérique
restent inchangés.
`startAdditionAt`, `startProductAt` et `startNegationAt` constituent une
occurrence composée fraîche avec des archives enfants reçues, jamais une
remise à zéro d'un enfant ou d'une occurrence composée déjà reçue. Dans les
API de commodité, un décalage nouvellement reçu commence son propre contexte
initial ; les API riches `translateRight`, `positiveProduct`, `multiplyRight`
acceptent les archives courantes explicites. Aucune minimalité riche, physique
ou inter-programmes n'est ajoutée.

La dépendance est acyclique : noyau des marges/dyadiques, runtimes
addition/produit, ordre exécuté et domaine quantitatif d'apartness, puis ce
nouveau module. Celui-ci consomme les lois multiplicatives et d'inverse déjà
fermées ; ni leur producteur, ni leur cohérence, ni leurs unités ne dépendent
du nouveau paquet d'ordre. Aucun ancien constructeur, contrat, énoncé ou
quantification n'a été modifié. Aucun passage par une présentation ou un
carrier n'entre dans ces nouvelles productions. Les transports d'ordre
restent les transports relationnels déjà prouvés sur Steps frais.

`Tests.RelationalRealOrderedField` contient 38 déclarations auditées : sommes
aliasées, archives/journaux non vides, cible exacte de l'action, conservation
des deux témoins et rôles, produit avec annulation non normalisée, reprise
depuis le successeur d'un produit antérieur, marge/budget, monotonie des deux
côtés, réflexion de translation, deux directions d'apartness et transport
par futurs numériques. Huit nouvelles fixtures fixent le site et le
diagnostic Lean refusant code/marge nus, apartness sans signe, facteur positif
absent, archive enfant initiale substituée au courant/successeur, direction
perdue et égalité des occurrences.

`check-real-ordered-field-codegen.py` analyse les routes C épinglées des deux
producteurs finis et, compositionnellement, l'orchestration de monotonie :
archives courantes, budgets issus des deux témoins, Steps/certificats exacts,
tentative partagée, extraction sans réexécution, rétention chronologique et
successeurs `a*c`, `b`, `c`. Vingt-sept mutations sont rejetées ; une duplication
valide est comptée deux fois même si son premier résultat est ignoré. Les
frontières explicites sont les runtimes natifs, cohérences et preuves
dyadiques déjà contrôlés séparément, puis ces producteurs lors du contrôle
de leur orchestration. Ce contrôle borné n'est ni une sémantique générale
du C, ni une certification des callbacks externes, ni une mesure physique.

Gates rejouées après stabilisation : build complet de 384 jobs,
`ALL_CONSTANTS_OK constants=35487 modules=381 generatedExceptions=697
writtenExceptions=0`. Les 8 déclarations du noyau, les 30 du module de lois
et les 38 des tests ont leurs audits individuels sans axiome ; chaque fichier
possède un bloc d'audit terminal unique. Le scan constructif et architectural
et la présence des artefacts compilés passent sur les 382 fichiers Lean.
Les quatre frontières d'import et leurs quatre autotests passent ; la
stratification et son autotest passent, avec 321 modules de production
inventoriés et aucun orphelin. Les 115 fixtures passent aux sites et diagnostics
exacts sans erreur supplémentaire. L'autotest des gates Bash/PowerShell passe
ses vingt cas : deux baselines de 115 fixtures et dix-huit mutations refusées.
Les onze contrôles codegen passent, dont les 27 mutations refusées du nouveau
contrôle. Le diff-check des fichiers suivis et nouveaux passe.

Les sept autotests documentaires passent ; `check-scientific-docs.py --static`,
`--lean`, `verify.ps1` et `verify.sh` sous Git Bash s'arrêtent tous avec le
`STALE_SOURCE: GODEL_RELATIONAL_SEQUENTIAL_COMPLETENESS` préexistant. Les
autres gates ont été exécutées séparément ; le statut des deux scripts globaux
n'est donc pas présenté comme un succès. Le registre, ses empreintes, les
passages canoniques/protégés, figures et statuts de revue restent inchangés.

### Densité dyadique et archimédianité exécutée — résultat du lot suivant

La portée est constructive et finie, à périmètre et base fixés. Pour tout
`origin : StrictOrder a b`, `produceDensity origin journal` produit un paquet
`Density origin journal` qui possède un code dyadique, son runtime constant
`q` et les deux témoins `StrictOrder a q` et `StrictOrder q b`. Ce n'est pas
une existence propositionnelle ni un choix de milieu reçu dans la requête.
Pour tout `source : Real P baseDepth`, toute archive courante native et tout
journal reçus, `produceNaturalBound source archive journal` produit deux
naturels `N` et `M`, deux runtimes constants exacts et les témoins strictement
orientés `-M < source` et `source < N`. C'est le sens archimédien obtenu ici :
chaque comportement reçu est strictement borné par un naturel, avec une borne
inférieure naturelle négative construite séparément. Aucune décision totale
de signe, totalité extensive, borne minimale ou conclusion de complétude
n'est ajoutée. Les API de commodité `dense` et `archimedean` appellent ces
mêmes producteurs avec le journal racine, et, pour `archimedean` seulement,
l'archive initiale du source. L'API riche conserve les archives courantes.

`DyadicDensity` ferme d'abord les obligations quantitatives. Une marge
`StrictSeparation p x y` possède l'échelle commune `s` et les composantes
signées relevées. `bisect` produit une seule fois
`qCode = ⟨x⁺_s+y⁺_s, x⁻_s+y⁻_s, s+1⟩`, ainsi que deux marges strictes à
`p+1`. Les lemmes `halfMarginLeft` et `halfMarginRight` consomment la marge
initiale par translation d'inégalités naturelles exactes ; aucune division
entière, normalisation opaque ou égalité d'occurrences n'intervient. Pour un
code fini reçu `c`, `naturalBounds` produit `N=c.positive+2` et
`M=c.negative+2`, avec deux marges strictement supérieures à une unité. Le
lemme `positiveComponentBound` utilise `n ≤ scaleNat n s` et `0 < 2^s` ; il
ne suppose aucune borne sur les composantes d'un code futur non normalisé.
Les bornes peuvent donc être larges en présence d'annulations, mais restent
finies, calculées et formellement suffisantes.

`RelationalRealDensity.densityProgram` et `boundProgram` sont des `Program`
à six phases, exécutés par le noyau constitutif existant. Le contexte reçu
possède respectivement le témoin `StrictOrder` exact ou le `Step` de sondage
exact. La recherche transmet ce contexte ; l'action lit sa ressource reçue
et appelle respectivement `bisect` ou `naturalBounds`. La préservation
consomme les deux marges du résultat de cette action. La décomposition,
continuation et mémoire transmettent la même sortie `Held`, dont l'exactitude
la relie au résultat de l'action. Ni la préservation ni le readout ne refont
la sélection. Le paquet `ExecutedRequest` conserve les phases, le journal
effectivement prolongé et la provenance. Les constantes sont construites
seulement depuis cette sortie stockée, non depuis la présentation du source.

Pour la densité, l'action consomme les deux Steps déjà possédés par `origin`.
Le runtime `q = dyadic P baseDepth action.readout` est produit une fois.
La première comparaison part de `origin.pair.left.next` et de la nouvelle
archive de `q`. La seconde utilise ce même `q`, depuis le successeur exact
de son Step dans la première comparaison, et `origin.pair.right.next`.
Les réponses sont à `p+6`. Les deux cohérences consomment explicitement les
Steps originaux et frais à `p+3`, autorisés par `origin.beyond`. Les réponses
constantes possédées donnent leurs `SameValue` exacts au code produit.
`strengthenSeparation` consomme alors chaque demi-marge à `p+1` et les deux
`Near (p+3)` nécessaires, donnant les deux marges finales à `p+3`. Le budget
de réponse est exactement trois bits plus fin. `Density.orders` extrait les
deux directions des classifications des mêmes tentatives. Les occurrences de
comparaison restent distinctes ; le second Step de `q` continue le premier,
il ne l'identifie pas et ne le reconstruit pas depuis ses valeurs.

Pour la borne archimédienne bilatérale, la chaîne exécutée est exactement :

```text
archive source courante -> sonde à 2 -> action de bornes stockée
  -> comparaison -M/source depuis probe.next à réponse 5
  -> comparaison source/N depuis lower.pair.right.next à réponse 5
```

Il n'y a qu'une sonde. Les deux constantes proviennent des deux naturels du
même résultat d'action stocké. Deux cohérences `Near 2` comparent cette sonde
aux deux étapes courantes effectivement possédées. Les marges initiales à 0
et ces proximités donnent les marges finales à 2, avec le budget `2+3=5`.
`NaturalBound.orders` consomme les classifications correspondantes, sans
repartir de l'archive initiale ou refaire une comparaison numérique séparée.

| Passage | Formation / exécution | Preuve consommée | Conservation / projection |
| --- | --- | --- | --- |
| Action de densité | Témoin source exact, deux Steps et marge reçus ; `Program` à journal courant | Demi-marges à `p+1` du même résultat `Bisection` | Action, préservation, continuation et mémoire restent possédées |
| Deux comparaisons de densité | Même runtime `q`, deux Steps `q` chronologiques, successeurs des sources | Cohérence reçue à `p+3`, exactitude des réponses constantes, deux transports de marge | Deux ordres orientés ; aucune égalité des occurrences |
| Action de borne | Une sonde réelle à 2 depuis l'archive courante ; deux naturels produits et stockés ensemble | Deux marges finies à 0, valides avec annulations | Résultat unique conservé avec son exécution et son journal |
| Comparaisons de borne | Chaîne source sonde → lower → upper, sans nouvelle sonde | Deux `Near 2` sur les Steps exacts, marges finales à 2 | Deux directions séparées, pas de décision globale de signe |
| Readout / live | Runtimes constants natifs créés à partir des codes produits | Lois et projections des constantes déjà établies | Paquet riche absent des fermetures live ; aucune minimalité riche ou physique |

Aucun nouveau service persistant ni modification de `Real`, `Service`,
`Coherent` ou d'un ancien énoncé n'est nécessaire. Les paquets de sélection
sont des ressources finies non persistantes ; les futurs sont ceux des
sources et constantes natives déjà exécutables. Le constructeur de constante
reçoit ici un code produit comme contexte fini, pas un réel extensif extrait
puis réemballé. Les projections présentation/carrier testées viennent après
les témoins relationnels, via les transports d'ordre déjà prouvés.

`Tests.RelationalRealDensity` contient 39 déclarations auditées : deux ordres
de densité, partage et réutilisation du même `q`, archives sources non vides,
journaux prolongés, action stockée exacte, étapes source chaînées, bornes
naturelles du sondage, deux signes, zéro/un, annulation non normalisée,
réponses live à deux précisions et projections aval. Dix fixtures fixent les
diagnostics/sites refusant marge nue, cible prescrite, résultat dyadique nu
à la place de l'action exécutée, naturel nu à la place du témoin d'ordre,
archives réinitialisées, mauvais successeur source et égalité d'occurrences.

`check-real-density-codegen.py` vérifie les routes C épinglées : un seul
`bisect` ou `naturalBounds`, un seul exécuteur, tous les callbacks de phases,
six phases du noyau, lecture du résultat stocké, une cible `q` / deux cibles
de borne, deux comparaisons et les successeurs exacts. Ses 27 mutations
refusées incluent des sélections valides dupliquées et ignorées, les remises
à zéro de `left-q.next`, `probe.next`, `lower-source.next` et du journal,
la perte des réponses/marge et les sous-budgets. Les frontières explicites
sont l'exécution native, la cohérence et les preuves quantitatives déjà
vérifiées dans Lean ; ce contrôle borné n'est ni une sémantique générale du C
ni un contrôle universel de callbacks ni un théorème de coût physique.

Gates finales : build complet de 387 jobs,
`ALL_CONSTANTS_OK constants=35682 modules=384 generatedExceptions=702
writtenExceptions=0`. Les 10 déclarations du noyau, les 16 du module exécuté
et les 39 des tests ont leurs audits individuels sans axiome. Les 385 fichiers
Lean passent le scan constructif et architectural, le contrôle du bloc d'audit
terminal unique et la présence des artefacts compilés. Les quatre frontières
d'import et leurs autotests passent ; stratification et autotest passent sur
323 modules de production sans orphelin. Les 125 fixtures passent à leurs
diagnostics et sites exacts, sans erreur supplémentaire. L'autotest des gates
Bash/PowerShell passe ses vingt cas : deux baselines de 125 fixtures et
dix-huit mutations refusées. Les douze contrôles codegen passent ; le nouveau
contrôle refuse ses 27 mutations pour les motifs attendus. Le diff-check
couvre les fichiers suivis et nouveaux.

Les sept autotests documentaires passent. `--static`, `--lean`, `verify.ps1`
et `verify.sh` sous Git Bash restent bloqués sur le
`STALE_SOURCE: GODEL_RELATIONAL_SEQUENTIAL_COMPLETENESS` préexistant ; leurs
autres gates ont été lancées séparément. Le registre, ses empreintes, les
passages canoniques/protégés, figures et statuts de revue restent inchangés.
La densité et ces bornes exécutées ne démontrent aucune complétude. Le lot
de raccord suivant, décrit ci-dessous, réutilise séparément la complétude
autoritative déjà disponible pour une `ExecutedCauchyFamily` reçue.

### Familles exécutées dans le porteur commun — raccord de complétude obtenu

La portée de `RelationalRealCauchy` est exactement celle de la base reçue :
pour tout `P`, toute profondeur de base et toute
`family : ProducedCompleteness.ExecutedCauchyFamily P baseDepth`, le module
expose les comportements `termReal family n`, le module monotone reçu
`family.modulus`, et `limitReal family`. Il ne postule ni ne reconstruit une
nouvelle complétude. Il ne reçoit pas une séquence arbitraire `Nat → Real`
accompagnée seulement d'une convergence de readouts. La réalisation d'une
telle entrée plus générale n'est pas établie par cet adaptateur et ne doit
pas être inférée de son nom `InternalCompleteness`.

`TermArchive family` est exactement l'archive accessible déjà utilisée par
le leaf `RuntimeReal.ofFamily family`. Pour un indice fixé `n`,
`termEnvironment family n` possède directement comme `Resource archive p`
le `AuthoritativeRuntime.RawSourceStep family archive.state
{ term := n, precision := p }`. Son unique appel à `performRawSource` exécute
`sourceProgram family.producer` depuis `archive.state.journal`. Le successeur
est le `step.next` de cette même ressource, avec
`Reachable.rawSource archive.reachable step` ; sa mémoire riche ajoute
`.rawSource step.execution`, et son journal est le journal complété de cette
exécution. L'événement riche conserve l'archive entrante, la précision et le
pas exact. Un terme puis une limite peuvent ainsi continuer la même archive
autoritative, sans remise à zéro ni conversion de présentation.

La fermeture live est `termLiveStep family.producer n`, dont les seuls
arguments statiques sont `SourceProducer` et `n`. Elle appelle l'interpréteur
commun `CommonRealRuntime.performReal` sur sa route `.source`. Le modulus du
petit `sourceEnvironment` est la fonction fermée `fun _ => 0`, jamais le
modulus réel ou une projection différée de la famille riche : la route source
ne le lit pas. `termLiveStep_is_source` prouve par `rfl` l'identité exacte des
résultats mémoire/événement avec la route source de `environmentOfFamily`.
Le contenu live est le `ReducedState` existant — profondeur et dernière
observation —, sans archive, certificat, loi de Cauchy ou témoin riche.
Le producteur reçu reste une frontière explicite : aucune propriété générale
de ses captures internes ou de son coût physique n'est prétendue.

`termNextProjection`, `termEventProjection` et les champs du service réalisent
exactement le contrat d'archive projeté par le contrat live ; le contrat riche
reste distinct. `termMemorySeparates` utilise la dernière observation et la
profondeur de départ de l'événement pour séparer les deux champs du
`ReducedState`. Les théorèmes génériques de réalisation et de minimalité
s'appliquent donc à **producteur et indice fixés**, uniquement au contrat live
et à l'archive après projection des événements. Il n'y a aucune minimalité
de l'archive riche ou inter-producteurs, ni égalité d'occurrences.

`termCoherent` consomme les deux `resource.execution` reçus avec
`ProducedSourceAt.sameTermExecutedNear`. `termUniform` compare deux résultats
possédés à la même précision, via leur `RawSourceStep.readoutExact`.
Le champ `CertifiedService.uniform` a toujours son énoncé canonique ancien,
et `termCertificate.uniform` le dérive par
`termUniform family term step (canonicalStep _ precision)`. Cette référence
canonique appartient à la preuve de l'égalité de codes ; elle ne remplace pas
le Step reçu dans la production ou dans les deux lois de famille ci-dessous.
`currentReadout` sur `termReal` passe précisément par cette certification.
L'égalité est en `Prop`, effaçable ; sa formation ne prouve ni la présence ni
l'absence d'un appel source supplémentaire dans le code compilé, à contrôler
séparément par codegen. Ces certifications sont dérivées, pas des hypothèses
terminales ajoutées. `termReal` utilise `.certified` ; aucun constructeur de
`Real`, aucun ancien contrat ou énoncé ne change.

La limite est strictement
`limitReal family := .leaf (RuntimeReal.ofFamily family)`. Chaque Step
limite courant exécute donc la source diagonale puis le regroupement,
l'action qui produit sa cible, sa continuation et sa mémoire déjà établis.
Il possède `limitProduction.source.execution` et l'exécution de regroupement
depuis le journal complété de cette source. Le successeur stocke cette
`limitProduction` exacte et installe son `OwnedTarget.limit`. Le raccord
n'ajoute pas de nouveau producteur limite ni de cible dans la requête.

Les deux lois ont la portée reçue suivante, avec des `PrecisionExtension`
positives, deux archives courantes quelconques de ces services et leurs
Steps effectivement produits :

| Loi | Hypothèses quantitatives | Ressources réellement consommées | Conclusion |
| --- | --- | --- | --- |
| `termsCauchy` | `modulus p ≤ n,m` et `p ≤ r,s` | `first.resource.execution`, `second.resource.execution`, leurs requêtes et journaux exacts | `Near p first.code second.code` |
| `termLimitNear` | `modulus p ≤ n` et `p ≤ r,s` | Exécution du Step terme reçu et `limitStep.resource.response.limitProduction.source.execution` | `Near p termStep.code limitStep.code` |

Pour la convergence, `sourceAtExact` identifie l'indice diagonal possédé avec
`modulus s`. `modulusMonotone limitBeyond` construit exactement l'extension
de `modulus p` à cet indice. `family.cauchy` reçoit alors les deux exécutions
ci-dessus. `limitStepReadout` ne fait que déplier le paquet réponse reçu ;
`readout_is_source` vient de l'action de regroupement effectivement possédée.
Les corps de `termsCauchy` et `termLimitNear` ne substituent aucun
`readoutsNear`, `executeReal`, `stepAt` ou pas canonique aux deux exécutions
reçues. Cette propriété de leur corps ne contraint pas celui du callback
`family.cauchy` reçu, dont les dépendances doivent être décrites séparément
pour chaque réalisation, notamment après transport numérique de famille.
Le témoin normalisé source–cible et son transport hétérogène
restent conservés par le paquet limite ancien ; cette nouvelle preuve ne
les remplace pas par une reconstruction. Le paquet
`internalCompleteness family : InternalCompleteness family` contient les
termes, le module, la limite, leurs égalités d'origine et ces deux lois
constructivement dérivées.

`Tests.RelationalRealCauchy` comporte 39 déclarations auditées : termes
successifs sur archives/journaux non vides, changement d'indice sur la même
archive, pas limites successifs, profondeurs `+6`/`+12`, conservation
chronologique des ressources, action et cible installée exactes, témoin
normalisé, projections de Step et de futurs finis, mémoire à environnement
fixé, cohérence/uniformité, Cauchy/convergence sur les Steps courants,
composition avec addition/produit et réemploi d'une famille concrète de test
déjà existante. Les tests ne sont aucune nouvelle entrée de production.
Neuf fixtures fixent sites et diagnostics refusant code nu, reset de terme,
reset de limite, source nue substituée à un Step limite, oubli du module,
archive/famille riche en live, égalité d'occurrences et généralisation à une
séquence arbitraire `Nat → Real`.

`check-real-cauchy-codegen.py` suit le callback concret du terme courant
jusqu'à son unique source/exécuteur et ses requête/journal exacts. Il contrôle
les deux exécutions transmises à Cauchy, la source possédée et le renforcement
monotone transmis par la convergence, la projection du résultat détenu,
la mise à jour `.rawSource`, et les captures live `producer + n` seules.
Il suit aussi la vraie route leaf/`completeViaRuntime` jusqu'à la branche
limite de `executeResponse`, sélectionnée depuis son constructeur épinglé,
puis ses uniques exécutions source et regroupement. Vingt mutations sont
refusées, dont deux duplications valides avec résultat ignoré. Les frontières
nommées sont l'exécuteur constitutif, les corps des programmes source et
regroupement, les projections/readouts, la mise à jour riche native et les
lois de la famille reçue, dont Lean ferme séparément les contrats. Ce n'est
ni une sémantique C universelle ni une certification de tout callback externe.
L'unicité comportementale de la limite et les transports terminaux restent
hors de ce lot.

Gates finales du raccord : build ciblé du module (40 jobs), tests ciblés
(130 jobs), puis build complet de 389 jobs avec
`ALL_CONSTANTS_OK constants=35797 modules=386 generatedExceptions=704
writtenExceptions=0`. Les 20 déclarations du module et les 39 des tests sont
auditées individuellement sans axiome. Les 387 fichiers Lean passent le scan
constructif et architectural, le contrôle du bloc d'audit terminal unique et
la présence des artefacts compilés. Les quatre frontières d'import et leurs
quatre autotests passent ; stratification et autotest passent sur 324 modules
de production sans orphelin. Les 134 fixtures passent avec classe, site et
diagnostic exacts sans erreur supplémentaire. La catégorie de la nouvelle
fixture de séquence arbitraire est `dependent-type`, conformément au diagnostic
`Application type mismatch` réellement émis, et non `semantic-type`.
Les treize contrôles codegen passent ; le nouveau contrôle refuse ses vingt
mutations. L'autotest des gates de fixtures passe ses vingt cas : deux
baselines Bash/PowerShell de 134 fixtures et dix-huit mutations refusées.
Le diff-check couvre les fichiers suivis et nouveaux.

Les sept autotests documentaires passent. `check-scientific-docs.py --static`,
`--lean`, `verify.ps1` et `verify.sh` sous Git Bash sortent avec le code 1 sur
le `STALE_SOURCE: GODEL_RELATIONAL_SEQUENTIAL_COMPLETENESS` préexistant.
Les autres gates ont été exécutées séparément : les deux scripts globaux ne
sont pas présentés comme verts et aucune empreinte n'a été actualisée
mécaniquement. Le registre, les passages canoniques/protégés, les figures et
les statuts de revue sont inchangés. Aucun ancien fichier de preuve, ancien
énoncé ou contrat n'a été modifié pour ce raccord.

### Unicité de deux candidats de la même famille exécutée — obtenue

`RelationalRealLimitUniqueness.LimitCandidate family` reçoit un `Real`, un
seuil calculable `threshold : Nat → Nat` et une convergence positive. Cette
dernière consomme un Step terme courant et un Step candidat courant, sur
archives arbitraires, ainsi que les trois extensions explicites
`modulus p ≤ n`, `p ≤ termPrecision`, `threshold p ≤ response`, puis produit
`Near p termStep.code candidateStep.code`. L'interface ne reçoit ni
`Equivalent`, ni une cible limite prescrite, ni un readout préfabriqué.
Le candidat `authoritative family` est exactement `limitReal family` : son
seuil est l'identité et sa convergence est exactement `termLimitNear family`.

Pour deux candidats reçus `first` et `second`, le seuil commun est

```text
T(p) = first.threshold(p+1) + second.threshold(p+1).
n(p) = family.modulus(p+1) ; précision du terme = p+1.
```

Les extensions `firstExtension` et `secondExtension` composent les inclusions
positives dans cette somme avec les budgets de réponse reçus par la requête.
`mediate` exécute lui-même une fois chacun des trois Steps depuis les trois
archives reçues. Ce comptage des appels explicites du médiateur ne compte pas
les formations ou calculs internes aux callbacks de convergence reçus ; leurs
corps ne sont pas imposés par l'interface générique. Son paquet `Mediation`,
à constructeur privé, retient ces archives comme données, les trois Steps,
leurs égalités d'origine à
`executeAt`, les deux convergences sur **le même** `termStep` possédé, puis
`Near.compose firstNear.symm secondNear`. Des champs d'exactitude identifient
ces trois témoins aux consommations effectivement effectuées. Le passage de
`p+1` à `p` est exactement celui de `Near.compose`, pas une estimation ajoutée
au seuil du candidat. Les deux Steps candidats restent deux productions,
y compris lorsque les comportements ou valeurs coïncident.

| Passage | Formation / exécution | Preuve consommée | Conservation / oubli |
| --- | --- | --- | --- |
| Candidat | Réel et seuil reçus ; loi sur Steps actuels quelconques | Convergence positive, sans équivalence supposée | Même famille exécutée, pas toute séquence `Nat → Real` |
| Médiation | Trois archives courantes ; une exécution terme et deux exécutions candidates | Les deux callbacks reçoivent le même terme à `modulus(p+1)` ; symétrie puis composition | Trois Steps et trois Near possédés avec leurs origines |
| Trace riche | Une seule `mediate` par requête ; récursion depuis les trois `.next` exacts | Chaque maillon garde ses deux convergences et sa proximité composée | Archive terme partagée même lorsque l'indice de terme change |
| Projection numérique | Steps candidats et Near déjà stockés | Aucune nouvelle convergence ni exécution | Oublie seulement le médiateur après constitution de la trace entière |
| Unicité terminale | Trace riche chronologique de toute la liste avant projection | `NumericalFutureEquivalent.toEquivalent` | Futurs numériques et `Equivalent`, jamais égalité des occurrences |

`UniquenessTrace` est une donnée en `Type`, avec récursion compilable sur la
liste de requêtes. Seule la génération automatique facultative de `sizeOf`
est localement désactivée pour cet inductif dépendant ; aucune quantification
de ses constructeurs ni d'un ancien énoncé n'est modifiée.
`produceTrace` produit une unique médiation par maillon puis continue les
trois successeurs. `toNumerical` réemploie les deux Steps candidats et le
Near composé stockés, sans `executeAt`. `numericalFutures` peut choisir une
archive terme initiale pour chaque liste, mais produit une seule trace riche
pour **toute** cette liste depuis les archives candidates arbitraires reçues.
`uniqueness`, `unique` et `authoritativeUnique` dérivent `Equivalent` depuis
ces futurs, jamais depuis la réflexivité ou `Equivalent.toFutures`.

`Tests.RelationalRealLimitUniqueness` comporte 35 déclarations auditées.
Il oppose le leaf autoritatif à un arbre `.certified` syntaxiquement distinct
qui réemploie exactement le service et la cohérence de ce leaf, sans
reconstruction de limite. Dans ce test, `currentReadout` intervient pour
certifier l'uniformité du service ; il n'apparaît pas dans les corps de la
médiation ou de l'unicité. Cette observation locale ne contraint pas les corps
des callbacks de convergence reçus par l'interface générique.
Deux requêtes de précisions 0 puis 2 changent l'indice médiateur ; une famille
concrète déjà existante vérifie `modulus 1 = 1` et `modulus 3 = 3`.
Les tests partent de trois archives non initiales, montrent les trois
successions, les profondeurs de journaux `+6` / `+12` / `+12`, le partage du
terme entre les deux lois, la trace riche à deux maillons et sa projection
exacte. Aucun test ne devient une nouvelle entrée de production.

Dix fixtures fixent sites et diagnostics refusant : candidat sans convergence,
réflexivité substituée aux deux candidats, familles différentes, deux
tentatives d'identifier les occurrences depuis Near/Equivalent, reset de
chacune des trois archives et code nu substitué à l'un des Steps. Le reset
terme utilise exactement le même `termReal family (modulus (p+1))` des deux
côtés : son échec porte sur l'archive initiale contre `packet.termStep.next`,
pas sur un indice de terme différent.

`check-real-limit-uniqueness-codegen.py` contrôle quatre routes C épinglées :
médiation, branche cons de production de trace, projection de cette branche,
et construction du futur sur toute une liste. Les calculs numériques suivis
sont `p+1`, les deux seuils et leurs extensions positives ; une frontière
locale explicite interprète l'addition de naturels sans changer l'analyseur
partagé. Les callbacks sont fermés par leurs arguments de frontière : les
deux reçoivent le même Step terme et leur Step candidat exact. Les 22
mutations refusées couvrent les trois archives des exécutions, dix arguments
de convergence (archives/Steps/budget), les trois continuations, la direction
et la seconde proximité, le remplacement de la trace, deux duplications
valides dont le résultat est ignoré et une réexécution en projection.
Les frontières déclarées sont l'exécution native des `Real`, `Step.next`,
les corps reçus des callbacks/rates, Near.symm/compose et la queue récursive.
Le contrôle suit une branche cons et ses arguments de récursion, pas un
déroulement universel de toutes les listes ni une sémantique générale du C.
Ce lot ne crée aucun service persistant, nouveau runtime, nouvelle mémoire
live ou notion de minimalité. Aucun contrat antérieur n'est modifié.

Les 17 déclarations centrales et les 35 des tests ont leurs audits individuels
sans axiome ; les builds ciblés ont réussi (41 et 132 jobs). Les quatre
routes codegen et leurs 22 refus de mutations ont réussi. Le build global
réussit sur 391 jobs, avec
`ALL_CONSTANTS_OK constants=35943 modules=388 generatedExceptions=707
writtenExceptions=0`. Les 389 fichiers Lean passent le scan constructif et
architectural, le contrôle du bloc d'audit terminal unique et celui des
artefacts compilés. Les quatre frontières d'import et les quatre autotests
du parseur passent ; stratification et autotest passent sur 325 modules de
production sans orphelin. Les 144 fixtures passent avec classe, site et
diagnostic exacts sans erreur supplémentaire. Les quatorze contrôles codegen
passent. L'autotest des gates de fixtures passe ses vingt cas : deux
baselines Bash/PowerShell de 144 fixtures et dix-huit mutations refusées.
Le diff-check couvre les fichiers suivis et les 129 fichiers nouveaux de
l'arbre partagé, sans attribuer les lots préexistants à ce seul lot.

Les sept autotests documentaires passent. `--static`, `--lean`, `verify.ps1`
et `verify.sh` sous Git Bash sortent avec le code 1 sur le
`STALE_SOURCE: GODEL_RELATIONAL_SEQUENTIAL_COMPLETENESS` préexistant. Les
autres gates ont été exécutées séparément ; les scripts globaux ne sont pas
présentés comme verts. Le registre et ses empreintes n'ont pas été actualisés.
Registre, passages canoniques/protégés, figures et statuts de revue restent
inchangés. Aucun ancien fichier de preuve, énoncé, constructeur ou contrat
n'a été modifié. Ce lot s'arrête ici, avant les transports terminaux et la
correspondance finale ; il ne prouve aucune complétude pour une séquence
arbitraire de `Real` ni aucune identification des histoires riches.

Les lots opposé/groupe additif, multiplication, apartness/ordre, inverse sous
apartness, compatibilités de corps ordonné à équivalence près et
densité/archimédianité exécutées, ainsi que le raccord de la complétude de la
classe `ExecutedCauchyFamily` au porteur commun et l'unicité comportementale de
deux candidats convergeant vers cette même famille, sont obtenus sur l'arbre de chantier dans les
portées exactes ci-dessus, sous réserve des résultats des gates rapportés.
Le lot de transport comportemental des familles et des limites est décrit
ci-dessous ; les transports individuels d'opérations et d'ordre déjà fermés
sont réemployés. À cette étape du chantier restaient ensuite le paquet final
de correspondance avec la classe effective choisie, désormais construit plus
bas, puis la gate distincte de couverture qui reste ouverte avant toute
annonce concernant tous les réels usuels.

La couverture des familles générales de comportements composés ne fait pas
partie de ce seul raccord source. Elle est requise par la correspondance
terminale ; le premier raccord natif numérique décrit plus bas ne la ferme pas. Aucun
passage ne transforme l'ancien adaptateur en complétude pour une séquence
nue de `Real`, sans loi Cauchy sur ses Steps actuels.

### Transport effectif des familles et des limites — implémentation du lot

`RelationalRealFamilyTransport` implémente les interfaces `EffectiveFamily`,
`readoutFamily`, `realizeFamily`, `PresentationLimit`, `reflectLimit`,
`realizeLimit` et `preserveLimitAt` décrites ci-dessous. Les prototypes stdin
ont été remplacés par des déclarations auditées et des tests durables.
Les transports d'addition, opposé, multiplication, inverse sous apartness,
ordre et apartness déjà fermés doivent être réemployés, non dupliqués.
Ce lot n'est ni le paquet final de correspondance, ni la gate des
réels usuels, ni une extension à une séquence arbitraire `Nat → Real`.

La cible de famille effective doit recevoir des termes
`Nat → EffectiveDyadicPresentation`, leur cohérence, un module monotone de
famille et une loi de Cauchy uniforme : pour `modulus p ≤ n,m` et `p ≤ r,s`,
les réponses `terms n r` et `terms m s` sont `Near p`. La réalisation construit
un vrai `SourceProducer`, calculant l'approximation du terme et de la précision
de la requête, puis une vraie `ExecutedCauchyFamily`. Sa loi de Cauchy consomme
les deux exécutions source reçues et leurs actions stockées avant la loi
numérique reçue. Cette consommation n'est pas limitée aux réécritures en
`Prop` : les deux `readout` stockés sont lus avant l'appel numérique ; leurs
échelles calculent les deux coordonnées `common - ownedCode.scale` du Near
retourné. `alignOwnedNear_exact` prouve que ce réalignement conserve exactement
le témoin numérique transporté : même échelle commune, mêmes lifts,
`precisionExtra` et bornes dirigées. Il n'ajoute ni padding ni dépendance à
un journal artificiellement inspecté. Les égalités d'extrémités et les preuves
des bornes restent propositionnelles et ne sont pas observées en C.
La limite reste exclusivement `limitReal` de cette famille,
donc la source diagonale, le regroupement, la cible produite et son
installation autoritatives existantes. Aucune limite n'entre dans la famille
comme cible prescrite.

**Portée des deux directions et de leurs allers-retours.** Depuis une famille
effective `f`, le readout de `realizeFamily P d f` restaure ponctuellement les
codes de ses termes et son module. Depuis une famille exécutée `F`, le
retour `F' := realizeFamily P d (readoutFamily F)` restaure
définitionnellement son producteur et son module, sans égalité extensionnelle
de fonctions. Les codes et le comportement numériques des termes sont
préservés : `effectiveReturnAt`, `relationalReturnAt`, `effectiveRoundtrip`,
`relationalRoundtrip`, `realizedTermEquivalent` / `realizedTermFutures` et
`relationalTermRoundtrip` / `relationalTermFutures` fournissent les exactitudes
et équivalences avec seuil identité. Ces propriétés ne sont ni une égalité de
familles riches ni une conservation de leurs preuves. La donnée positive `cauchy`,
les témoins `Near` en `Type`, les journaux, archives, occurrences et histoires
ne sont pas conservés ou récupérés par ce transport. La loi reconstruite
projette les exécutions reçues puis emploie la loi numérique de `readoutFamily` ;
celle-ci instancie des productions canoniques de `F`, pas ses archives
courantes arbitraires. Cette perte est propre au transport étudié, pas une
impossibilité universelle de conserver davantage dans une autre interface.
Elle exprime le caractère aval et appauvri du readout, sans inverser les
primitives relationnelles.

Un contre-test durable sans axiome distingue effectivement ces données : pour
une famille de codes nuls dont `cauchy` ajoute la profondeur relative du
premier journal à `Near.scale.common` par `liftCommon`, les mêmes exécutions
courantes après six phases donnent, à précision 0, une échelle 6 sous
`F.cauchy`, mais 0 sous `F'.cauchy`.
Les deux valeurs sont calculées par `rfl` et leur égalité conduit à `Empty`.
`directScale`, `reconstructedScale` et `cauchyDataNotRecovered` des tests
verrouillent les valeurs 6 et 0 et leur distinction, même après le réalignement
exécutable des coordonnées. La proximité numérique demeure valide ; l'identité
de son témoin positif n'est donc pas un corollaire de la restauration du
producteur et du module.

**Route A obligatoire pour l'aller-retour relationnel des limites.** Pour une
famille exécutée reçue `F`, poser
`F' := realizeFamily P d (readoutFamily F)`. Le candidat `candidateA` est un
`LimitCandidate F'` dont `real := limitReal F` et dont le seuil est l'identité.
Il reçoit un Step terme courant de `termReal F' n` et un Step courant de
l'ancienne `limitReal F`, sur leurs archives arbitraires. Le producteur et le
module de `F'` sont restaurés définitionnellement ; les deux restaurations
ont été vérifiées par `rfl`, sans égalité extensionnelle de fonctions.
La convergence de `candidateA` applique directement `F.cauchy` à
`termStep.resource.execution` et à
`limitStep.resource.response.limitProduction.source.execution`, avec les
requêtes et journaux réellement possédés. `sourceAtExact` et
`F.modulusMonotone` fournissent l'extension vers la diagonale reçue ;
`limitStepReadout` et `readout_is_source` projettent cette même production.
Aucun Step canonique ne remplace l'un de ces deux Steps. Ensuite seulement,
`authoritativeUnique candidateA` donne

```text
Equivalent (limitReal F') (limitReal F)
× NumericalFutureEquivalent (limitReal F') (limitReal F).
```

La médiation et sa trace sont celles du lot d'unicité déjà établi : même
terme partagé, deux convergences et trois successeurs courants. Il faut
distinguer les deux convergences de `authoritativeUnique candidateA` :

- celle de `candidateA` transmet directement les deux ressources actuelles
  ci-dessus à `F.cauchy` ;
- celle de `authoritative F'` est `termLimitNear F'` : elle transmet les
  exécutions courantes à `F'.cauchy`, puis la loi numérique reconstruite par
  `readoutFamily F` peut mobiliser les productions canoniques de `F`. Elle ne
  consomme donc pas directement le témoin riche original sur ces archives.

Pour ces deux seuils identité, le seuil de l'unicité à précision `p` est
`(p+1) + (p+1)` et le terme partagé a l'indice `F.modulus (p+1)` et la précision
`p+1`. La projection `toNumerical` réemploie les Steps candidats et le Near
composé stockés sans nouvelle exécution dans son propre corps ; cela ne dit
pas que les corps des deux convergences sont exempts de références ou de
productions canoniques. L'égalité définitionnelle du producteur n'identifie
ni les familles, ni les archives, ni les témoins Cauchy, ni les occurrences,
et ne prouve pas un coût compilé identique.

**Route B directe interdite.** Remplacer ce candidat réel par
`ofPresentation P d (toPresentation (limitReal F))` ne permet pas d'appliquer
directement `F.cauchy` à sa source interne. Cette source est une exécution de
`sourceProgram (presentationToRuntime P d (toPresentation (limitReal F))).family.producer`,
pas de `sourceProgram F.producer`. Son calcul ignore l'indice de terme et lit
la présentation limite ; une égalité de codes ne transforme pas son exécution
en exécution de l'autre programme. Une seconde obstruction indépendante porte
sur l'indice diagonal : `production.sourceAt.request.term` provient du module
de cette famille synthétique de présentation, pas de `F.modulus`.
`F.modulusMonotone candidateBeyond` fournit une extension vers
`F.modulus response`, pas vers cet indice synthétique. Le mismatch de
programme ne résume donc pas le mismatch d'indice/module diagonal. Le
prototype isolant la conversion d'exécution a échoué sur le premier mismatch ;
les deux fixtures `FamilyPresentationSourceCannotUseOriginalProgram` et
`FamilyPresentationDiagonalCannotUseOriginalModulus` verrouillent séparément
ces obstructions au site et diagnostic attendus. B ne peut être
qu'une réalisation
numérique aval séparée, avec convergence reçue ou dérivée explicitement et
raccordée à ses Steps, jamais le raccourci de la route A ni un remplacement
par le seul aller-retour numérique individuel.

**Préservation riche et projection numérique globale distinctes.** La voie
riche a la forme `preserveLimitAt candidate p n r s termStep
candidateStep ...` : les deux Steps sont reçus sur archives courantes, les
trois extensions sont reçues, `candidate.converges` consomme ces mêmes Steps,
puis `currentReadout` raccorde leurs codes aux présentations par une égalité
propositionnelle, avec les références canoniques décrites ci-dessous.
`reflectLimit` et `realizeLimit` reçoivent aussi les Steps
courants dans leur callback de convergence ; ils appliquent la loi numérique
positive reçue et raccordent ses extrémités. Aucun appel explicite à
`executeReal` ou `executeAt` n'y remplace ces Steps reçus. Cela n'exclut pas
une formation canonique dans le raccord propositionnel `currentReadout`.
Ses cinq branches doivent être distinguées : `certified` passe par
`certificate.uniform`, qui, pour `termReal`, utilise
`termUniform ... step (canonicalStep ... precision)` ; `leaf` passe par
`leafCurrentReadout` et `limitStep_readout_eq`, qui raccordent le Step reçu
à `stepAt` / `perform` depuis l'état initial. `add` utilise `add_readout_exact`,
dont le corps forme `produceAddition` depuis les deux archives initiales et
le journal racine ; `neg` utilise de même `neg_readout_exact` et
`produceNegation` depuis l'archive initiale et le journal racine. Ces deux
branches appliquent aussi récursivement `currentReadout` aux sous-Steps reçus.
`mul` lie explicitement `canonical := produceMultiplication ...` depuis les
deux archives initiales et le journal racine, puis emploie `currentReadout`
sur les raffinements courants et canoniques ainsi que les sondages courants.
La distinction s'applique donc aussi récursivement aux comportements composés.
Ces références de preuve ne sont pas des Steps courants substitués aux
arguments reçus. Les égalités en `Prop`
peuvent être effacées ; l'absence d'un appel supplémentaire dans le code
compilé reste une obligation codegen, jamais une conclusion tirée du seul
terme de preuve. Les calculs internes à la loi numérique reçue doivent aussi
être distingués de ces raccords propositionnels.

Une loi numérique globale `PresentationLimit` ne reçoit, elle, que les indices
et extensions, pas de Steps. Le simple remplacement de son callback par
`candidate.converges` est mal typé : il manque les deux ressources. Une
commodité globale `preserveLimit` exécute de nouveaux Steps depuis les archives
initiales déclarées, les retient dans `LimitObservation` construit par
`observeLimit`, puis partage ces mêmes productions avec la preuve et la
projection. Les égalités d'origine et de proximité portent sur ces champs
exactement stockés. Elle ne
doit pas être présentée comme la préservation riche de Steps déjà reçus.
De même, la loi pure de readout d'une famille est distincte de sa projection
sur Steps courants : l'instanciation des productions canoniques définissant
les readouts n'est pas une consommation d'archives arbitraires reçues. La
convergence de `candidateA` utilise directement `F.cauchy` sur les ressources
reçues, pas cette instanciation numérique comme substitut. La convergence de
`authoritative F'` utilise en revanche la loi reconstruite décrite ci-dessus ;
le résultat d'unicité reste numérique et ne récupère pas par ce transport la
donnée Cauchy de `F`.

`PresentationLimit` doit conserver une convergence positive au domaine exact
de `LimitCandidate` : `modulus p ≤ n`, `p ≤ termPrecision` et
`threshold p ≤ response`. Une convergence avec un autre seuil d'indice n'est
pas supposée satisfaire ce contrat ; son raccord quantitatif demanderait une
preuve supplémentaire, sans changement silencieux du contrat ancien.

**Adaptateur carrier sans cofinalité cachée.** Une famille de carriers peut
recevoir sa loi sur les réponses brutes, avec les extensions
`(terms n).modulus p ≤ r` et `(terms m).modulus p ≤ s`. Sa normalisation choisit
exactement les réponses `(terms n).modulus r` et `(terms m).modulus s`, et
consomme seulement les deux `modulusMonotone` appliqués à `p ≤ r,s`. Aucune
inversion, croissance stricte ou cofinalité du module propre à un terme n'est
requise. Le test durable `boundedFamily`, dont les modules de termes et de
famille valent constamment zéro, est réalisé par `realizeCarrierLimit` ;
`boundedNotCofinal` prouve positivement vers `Empty` l'impossibilité d'une
extension de 1 vers ces modules. `CarrierLimit` porte exactement sur les
présentations normalisées, pas sur une inversion des indices bruts.
L'aller-retour préserve
exactement les présentations normalisées et compare les carriers bruts à
l'équivalence existante, jamais par égalité des suites ou des occurrences.

Tests durables et obligations pérennes de contrôle du lot :

- route A depuis archives terme et ancienne limite non initiales, deux
  précisions et une liste de requêtes ; les deux exécutions source exactes
  de `candidateA` doivent atteindre directement `F.cauchy` ; vérifier
  séparément le passage de `authoritative F'` par la loi reconstruite, le
  même terme partagé et la continuation des trois successeurs de la trace ;
- deux allers-retours comportementaux/numériques des familles : producteur
  et module restaurés définitionnellement côté relationnel, codes ponctuels
  exacts et équivalences uniformes des termes et de leurs futurs ; ne pas
  déduire une loi diagonale d'équivalences terme par terme à seuils
  incontrôlés, ni une égalité des familles ou de leurs preuves ;
- contre-test positif distinguant les témoins Cauchy sur un journal courant
  et sur un journal canonique, et fixtures refusant d'en déduire l'identité
  des `Near` en `Type` ou la récupération des histoires/archives depuis le
  seul aller-retour numérique ; ces refus n'énoncent pas une impossibilité
  universelle de toute autre interface plus riche ;
- deux fixtures distinctes isolant respectivement le mismatch de programme de
  B et son mismatch d'indice/module diagonal ; fixtures refusant le
  remplacement d'un Step
  par un code, le reset de chaque archive, une mauvaise famille, une loi de
  convergence absente, une préservation globale dépourvue de ses Steps et
  l'identification des occurrences depuis Near ou Equivalent ;
- tests positifs du carrier à module borné/non cofinal et de son aller-retour
  normalisé ; aucune hypothèse de cofinalité ajoutée pour faire compiler ;
- codegen distinguant les raccords riches sans appel explicite substituant
  un nouveau Step, la formation canonique propositionnelle possible de
  `currentReadout`, et la commodité globale qui produit explicitement ses
  Steps une fois ; contrôler séparément l'absence d'appels compilés
  supplémentaires sur les routes annoncées, sans la déduire de l'effacement
  possible des preuves, avec des cas `leaf`, `certified`, `add`, `neg`, `mul`
  et leurs compositions récursives, pas seulement des feuilles ou termes.
  Mutations de duplication, reset, remplacement
  d'exécution, journal, requête et médiateur partagé ; transmission directe
  des deux ressources reçues à `F.cauchy` dans `candidateA`, sans route B,
  et analyse distincte de la loi reconstruite de `authoritative F'`.
  Les corps des lois reçues restent une frontière déclarée : ni l'absence
  universelle de calcul interne, ni leur coût ne sont certifiés par ce
  contrôle borné ;
- vérification de la nouvelle réalisation effective : calcul au terme et à
  la précision reçus, action/source unique, route source puis regroupement,
  cible produite/installée et captures live compactes. Les fonctions
  effectives reçues restent une frontière déclarée, pas une certification
  universelle de leurs captures internes ou de leur coût.

L'ordre de fermeture respecté est : interfaces effectives et exactitudes des
termes ; deux directions et allers-retours numériques de familles, avec
inventaire des données riches non conservées ; route A et unicité avec les
deux dépendances de convergence séparées ; raccords numériques de candidats
distincts avec leurs Steps reçus et leurs références canoniques de preuve ;
puis seulement corollaires aval manquants. Aucun paquet terminal de
correspondance n'est annoncé dans ce lot. La route A est `returnedCandidate` ;
`relationalLimitRoundtrip` consomme `authoritativeUnique` et donne les deux
équivalences déclarées. `returnedAuthoritative` expose séparément l'autre
convergence reconstruite. Le contre-test Cauchy précise une perte de donnée
positive par ce transport, pas une impossibilité universelle.

Les seuls nouveaux `HEq` sont ceux de `projectLimitNear_heq` et du test
`observedNearNotReconstructed` : ils réindexent le même Near par les égalités
propositionnelles de ses deux codes d'extrémité. Ils n'identifient aucune
ressource, archive, famille ou occurrence ; `alignOwnedNear_exact` est une
égalité du certificat numérique aux coordonnées inchangées, pas d'histoires.

#### Non-perte locale et vérifications du lot

La comparaison SHA256 avec l'arbre sale figé avant ce lot conserve exactement
les trente modules antérieurs de `Constitution/Reals` et les douze modules
antérieurs `Tests/RelationalReal*`. Aucun ancien énoncé, constructeur,
quantification, contrat ou corps de preuve n'est modifié. Hors du plan, les
six fichiers d'intégration ne contiennent que des ajouts : retirer en mémoire
les nouveaux imports, audits, lignes de manifeste et appels codegen restitue
leurs six empreintes initiales. Parmi les 624 fichiers préexistants, 617 sont
octet-identiques ; les sept autres sont ces six fichiers et ce plan. Dix-neuf
fichiers sont ajoutés : module, test, script codegen et seize fixtures.

| Passage | Données effectivement consommées | Non-perte et frontière |
| --- | --- | --- |
| Réalisation de famille | Terme et précision reçus ; deux exécutions et actions stockées ; deux échelles utilisées avant/après la loi numérique | Vrai producteur ; module reçu ; aucun ancien contrat remplacé ; loi riche reconstruite, non récupérée |
| Route A | Deux sources actuelles de l'ancien producteur, requêtes/journaux exacts, diagonale et monotonicité | Ancien `cauchy` directement consommé de ce côté seulement ; autre convergence reconstruite explicitement séparée |
| Limites et futurs | Steps reçus, ou deux nouvelles productions possédées par `LimitObservation` ; trace d'unicité avec médiateur partagé | Pas de replay explicite substitué dans le raccord riche ; pas d'égalité d'occurrences ; trois successeurs conservés avant projection |
| Mémoire | Routes source/limite et contrats des services antérieurs réemployés | Aucun nouveau service persistant ni contrat mémoire ; aucune minimalité riche, physique ou inter-environnements ajoutée |
| Carrier | Réponses aux modules propres et leurs deux monotonies | Aucune cofinalité/inversion ; équivalence numérique, pas identité des indices bruts ou des familles |

Les 48 déclarations du module et les 68 des tests sont auditées sans axiome.
Le build ciblé des tests réussit sur 156 jobs ; le build global réussit sur
393 jobs avec `ALL_CONSTANTS_OK constants=36206 modules=390
generatedExceptions=712 writtenExceptions=0`. Les 391 fichiers Lean passent
le scan constructif et architectural, le contrôle de l'unique bloc d'audit
terminal et celui de la présence des artefacts compilés. Les quatre frontières
d'import et leurs quatre autotests passent ; stratification et son autotest
passent sur 326 modules de production sans orphelin. Les 160 fixtures passent
avec classe, site et diagnostic exacts, sans erreur supplémentaire ; seize
relèvent de ce nouveau lot.

L'autotest des gates de fixtures réussit ses vingt cas sur les sources figées :
deux baselines Bash/PowerShell de 160 fixtures et dix-huit mutations refusées.
Une première passe, pendant un rebuild, avait correctement refusé une classe
d'erreur inattendue sur `FamilyProducerRoundtripCannotIdentifyFamilies` côté
PowerShell (19 cas réussis sur 20) ; elle ne compte pas comme réussite.
La reproduction isolée a donné le Type mismatch attendu, puis la passe
complète sans build concurrent a réussi, sans modifier le fixture ni son
diagnostic/site attendu. Les deux résultats sont distingués, sans attribuer
une cause certaine au premier refus à partir de son seul résumé.

Les quinze scripts codegen passent. Le nouveau contrôle suit sept routes et
rejette 36 mutations : deux lectures des actions possédées avant le callback
numérique et leurs deux coordonnées réellement utilisées, slack conservé,
transmission directe de la route A, archives/Steps/budgets, observation à deux
productions uniques, duplications et exécutions supplémentaires, reconstruction
canonique distincte et normalisation aux modules propres. Les corps effectifs
reçus, l'exécution native et la récursion demeurent des frontières déclarées.
Les preuves `currentReadout`, les égalités d'origine et les bornes en `Prop`
ne sont pas observées en C. Les tests Lean couvrent séparément les cinq
constructeurs et une composition récursive ; le callback compilé générique,
dont les raccords propositionnels sont effacés, ne contient pas de nouvelle
exécution. Cette constatation ne certifie ni les calculs internes de lois reçues
ni leur coût.

Les sept autotests documentaires et les liens/structure des quarante documents
Markdown passent. `--static`, `--lean`, `verify.ps1` et `verify.sh` s'arrêtent
avec le code 1 sur le premier `STALE_SOURCE:
GODEL_RELATIONAL_SEQUENTIAL_COMPLETENESS` préexistant. Un recalcul séparé des
21 empreintes montre aussi `RUNTIME_EFFECTIVE_CAUCHY_REAL_CORRESPONDENCE`
périmée derrière ce premier arrêt. Ces deux entrées sont déjà périmées dans
l'arbre pré-lot reconstruit en mémoire ; aucune entrée périmée supplémentaire
n'est introduite. Les autres gates sont exécutées séparément, sans présenter
ces scripts globaux comme verts.
Le registre et ses empreintes, les passages canoniques/protégés, les figures
et les statuts de revue restent inchangés. À la clôture de ce seul lot de
transport, la gate 6 du paquet terminal et la gate 7 de couverture des réels
usuels restaient ouvertes ; le lot suivant traite la gate 6, pas la gate 7.
Le diff-check réussit pour les fichiers suivis et les 148 fichiers nouveaux
de l'arbre partagé, sans attribuer les 129 fichiers nouveaux préexistants à
ce seul lot. Aucun commit, push, fusion ou audit extérieur n'a été exécuté.

### Correspondance structurelle effective comportementale — gate 6

**Correction constitutive pour revue primaire.** La revue du premier prototype
avait bloqué les gates 4 (extension native) et 6 : sa réalisation depuis la vue
numérique ne retenait pas le Step natif dans le regroupement, et une diagonale
exécutée après coup ne réparait pas cette perte d'occurrence. La correction
décrite ici construit une nouvelle route riche, consomme et retient ce Step
exact avant projection. Les résultats numériques restent en aval ; le verdict
de clôture est soumis à la revue primaire de cette correction, pas déduit du
build. Le raccord source `ExecutedCauchyFamily` antérieur garde sa portée.

**Classe exacte et instance concrète.** `RelationalRealEffectiveCorrespondence`
construit `effectiveCorrespondence P d`, sans hypothèse terminale de
correspondance. Les objets sont le porteur fermé `Real P d` (ses cinq
constructeurs et leurs compositions), les `EffectiveDyadicPresentation`
exécutables avec cohérence positive, et les `EffectiveCauchyReal.Carrier`
munis de leur module monotone propre. Les équivalences sont respectivement
`Equivalent` / `NumericalFutureEquivalent`, l'équivalence positive des
présentations et celle des carriers. Aucun quotient, égalité d'occurrences,
identité de familles riches ni instance de corps total ne remplace ces relations.
La gate 7 de couverture des réels usuels reste ouverte.

Les applications exportées par `ApplicationMaps` sont reliées ponctuellement
aux fonctions `toPresentation`, `ofPresentation`, `toCarrier` et `ofCarrier`.
Ces égalités identifient les fonctions appliquées de cette construction, pas
les occurrences de deux exécutions ; elles n'emploient aucune extensionalité
de fonctions. Les autres blocs nomment ces mêmes fonctions fixes.
`effectiveCorrespondence` remplit concrètement tous les blocs depuis les
producteurs et théorèmes antérieurs ; leurs conclusions ne sont pas des
hypothèses de son constructeur de réalisation.

| Critère | Champs et réalisations concrètes |
| --- | --- |
| Applications et deux allers-retours | `applications` : présentations et carriers, retours réels à `Equivalent` et `NumericalFutureEquivalent`, retours numériques, préservation et réflexion de l'équivalence |
| Constantes dyadiques, zéro et unité | `operations.constants`, `realizeConstants`, `zero`, `one` ; `constantPreservation` et `constantRealization` consomment le théorème du runtime constant existant |
| Addition, opposé, multiplication | `operations.add/neg/mul`, `realizeAdd/Neg/Mul` et les six champs carrier correspondants |
| Inverse et domaine positif | `operations.inverse/realizeInverse`, champs carrier, et `relations.inverseDomain/carrierInverseDomain` ; aucune inverse sans apartness à zéro |
| Ordre et apartness | `relations` sépare préservation, réflexion sur images des applications et réalisation de présentations/carriers reçus ; les deux derniers passages exécutent des comparaisons fraîches aux archives déclarées |
| Lois de corps ordonné constructif | `ordered.laws` et `futureLaws`, avec préservation/réflexion universelle de l'équivalence et de l'ordre dans `applications/relations`, et les diagrammes opérationnels de `operations` |
| Densité et archimédianité exécutées | `ordered.density/bounds` sont les producteurs antérieurs ; `densityProjection/boundProjection` consomment leurs paquets reçus et projettent les ordres des mêmes cibles vers présentation et carrier |
| Familles-source et familles effectives | `families` : applications exactes, producteur et module, codes et allers-retours des termes, complétude-source et normalisation carrier sans cofinalité |
| Familles natives de comportements composés | `families.nativeReadout/nativeCompleteness/nativeUniqueness` : raccord général ci-dessous, sans réduire le carrier aux seuls termes-source |
| Limites et unicité | `limits` : domaine exact `PresentationLimit`, préservation riche, observation globale, réflexion/réalisation, route A et sa seconde convergence distincte, allers-retours de limites, trace riche et projection numérique |

Les lois ordonnées ne deviennent pas une décision totale. L'inverse garde son
domaine `Apartness x 0` ; la monotonie multiplicative garde les témoins
`Positive` orientés. Les champs universels de transport de l'équivalence et
de l'ordre s'appliquent aux lois natives reçues dans le paquet, et les
diagrammes d'opérations raccordent leurs deux lectures ; ils n'importent
aucune loi numérique pour produire rétroactivement le runtime.
Les tests `presentedAddCommutative`, `presentedMulCommutative`,
`unitTransported` et `positiveProductTransported` consomment ces champs.

**Raccord obligatoire des familles natives.** Le seul adaptateur
`ExecutedCauchyFamily → termReal` ne couvrait pas une famille de comportements
composés du porteur fermé. Le module `RelationalRealNativeCauchy` ajoute
`NativeCauchyFamily P d`, avec des termes `Nat → Real P d`, un générateur
séparé `kernels : Nat → NativeTermKernel`, un raccord exact de tout Step
courant au code du kernel, un module monotone et la loi positive suivante
sur deux Steps courants reçus :

```text
M p ≤ n, M p ≤ m, p ≤ r, p ≤ s
Step (terms n) aa r, Step (terms m) ba s
  -> Near p first.code second.code
```

Ce n'est donc ni une séquence nue ni une présentation fournie comme seconde
entrée de production. La cohérence de chaque terme vient de son `Real` ;
la loi de Cauchy inter-termes est une donnée relationnelle reçue.
`observePair` exécute une fois chaque terme aux archives explicites, possède
les deux Steps, conserve le même Near et en projette les extrémités.
`toEffectiveFamily` est une vue numérique aval ; sa commodité de Cauchy
déclare deux contextes natifs initiaux frais avant cette observation. Elle
ne récupère pas les archives antérieures.

`realizedFamily := realizeFamily P d (toEffectiveFamily family)` reste une
réalisation de la vue numérique aval. Elle ne constitue **pas** la limite
native : son producteur ne retient pas les occurrences natives. Le nouveau
module `RelationalRealNativeLimitRuntime` construit au contraire
`nativeLimit := Real.certified (nativeCertificate family)` depuis une
production source et un regroupement natifs. Aucune limite native ou
extensive ne figure comme cible d'entrée.
`realizedTermCode`, `realizedTermEquivalent` et `realizedTermFutures`
comparent les termes réalisés aux termes natifs, sans égalité de leurs
services, archives ou occurrences.

La ressource riche courante est `NativeArchive family` : banque dépendante
`(n : Nat) → Archive (environment (family.terms n))`, journal courant,
chronologie des productions et production installée. À précision `s`,
`nativeSourceProgram` reçoit `NativeSourceContext.archive`, lié à `bank (M s)`.
`searchNativeSource` lit ce champ reçu, exécute exactement une fois le terme
diagonal à `s`, puis réindexe seulement le paramètre archive de ce même Step
le long d'`archiveExact`. Il ne rebypasse pas le contexte reçu par la banque.
L'action et le Stored de la source retiennent ce Step.

`nativeGroupingProgram` reçoit cette exécution source exacte. Sa recherche
la transmet à l'action, qui construit une unique charge normalisée avec les
règles `LocalGrouping`. La spécification lit le code du Step possédé et son
Near positif est fourni par `family.cauchy` appliquée à ce même Step ; ce
n'est pas un `SameValue.refl.toNear`. Le `NativeTarget` est le résultat de
cette normalisation, pas une cible prescrite. Le Stored retient l'action,
sa source et sa cible ; `groupedSourceExact` prouve le partage exact de la
source. La seconde exécution continue le journal complété de la première.
Les deux wrappers ajoutent leurs six phases propres, sans compter les phases
internes du terme natif. `nativeNext` installe et archive la même production.
`readNativeInstalled` relit sa cible stockée, sans regroupement ni exécution.

La banque est mise à jour ponctuellement à `M s` par le `.next` de ce Step ;
tous les autres indices gardent leur archive possédée. Un changement d'indice
n'effectue aucun cast entre archives de termes différents. Une visite ultérieure
au même indice reprend son successeur conservé ; un indice jamais visité utilise
son entrée déjà déclarée dans la banque initiale/reçue. On ne prouve aucune
égalité de fonctions-banque, ni aucune identification de leurs histoires.

Pour la convergence, `observeLimit` reçoit le Step courant du terme à `n,r`
et le Step courant de la limite à `s`. Il **extrait** le diagonal de
`lim.resource.diagonal`, à l'archive exacte `la.bank (M s)` ; aucun argument
d'archive diagonale indépendant et aucun `executeAt` supplémentaire n'existent
dans cette route. `family.cauchy` consomme ce diagonal et le terme reçu ;
`modulusMonotone (p ≤ s)` donne `M p ≤ M s`. Le seul raccord final est
l'égalité du code normalisé avec celui de la source effectivement consommée.
`LimitObservation` conserve les deux Steps reçus, leur diagonal possédé,
l'archive et le Near reçu, puis son transport aux extrémités exactes.
`nativeAuthoritative` a seuil identité et réemploie cette observation.

`currentReadout` n'intervient plus dans cette convergence ni dans la constitution
riche. Il reste un pont propositionnel dans `nativeStep_liveCode`, le constructeur
de commodité `NativeCauchyFamily.ofTerms` et les vues numériques aval. Sa formation
canonique dans les cinq constructeurs reste celle détaillée plus haut ; elle ne
constitue pas une absence d'appel compilé. Aucun nouveau `HEq` n'est introduit.

`NativeCandidate` reçoit une loi de convergence sur Steps natifs et
candidats courants, pas l'équivalence terminale. `observeCandidate` possède
une contrepartie native nouvellement exécutée pour le Step terme-source
réalisé reçu, puis consomme celle-ci dans la loi native du candidat et
réaligne le Near aux codes des deux Steps reçus.
`asExecutedCandidate` déclare explicitement le contexte natif frais de
cette commodité. `nativeUnique` réemploie l'unicité de la famille réalisée ;
`nativeAuthoritativeUnique` compare son véritable candidat natif à l'autre
via `nativeUnique`. Le médiateur partagé de
sa trace chronologique est le même terme-source **réalisé** exécuté ; les
deux contreparties natives supplémentaires sont des observations distinctes.
Ce transport ne prétend ni partager une histoire native originelle entre
les deux callbacks ni continuer une archive native à travers des indices
de types différents. Les trois successeurs continués sont ceux du médiateur
réalisé et des deux candidats. La conclusion reste `Equivalent` et
`NumericalFutureEquivalent` depuis archives candidates arbitraires.
`nativeProducedLimitCorrespondence` compare seulement en aval la limite-source
de la vue effective à la limite native construite. `nativeCompleteness` expose
le service riche, cette projection numérique, la limite produite, les comparaisons
de termes, la convergence sans replay et l'unicité. `FamilyCorrespondence` porte
ce paquet ; `LimitCorrespondence` expose également le candidat natif exact et
sa projection, remplis concrètement dans `EffectiveCorrespondence`.

**Formation, exécution, preuve et oubli.** Les indices de Steps et les
égalités d'origine conservent les occurrences requises dans les paquets.
Les producteurs exécutent leurs Steps une fois dans les contextes déclarés ;
l'observation de convergence extrait ceux déjà possédés sans les réexécuter.
Les observations numériques de commodité qui exécutent des contreparties
fraîches sont distinguées de cette route constitutive.
Les raccords numériques utilisent séparément `currentReadout` en preuve.
Les projections peuvent oublier les ressources seulement après cette
construction ; elles ne les récupèrent pas en sens inverse.
La donnée positive Cauchy, les Near en Type, journaux, archives et histoires
ne sont pas conservés/récupérés par les allers-retours numériques.
Le contre-test durable ancien `6/0` est réemployé via
`directSix`, `reconstructedZero` et `richCauchyLoss` ; il ne démontre
pas une impossibilité universelle de tout autre transport enrichi.
La route A, ses deux convergences distinctes, les deux obstructions de B,
le domaine exact de `PresentationLimit` et la normalisation des carriers
aux modules propres ne sont pas modifiés.

Le nouveau service persistant déclare un contrat live **numérique** : mémoire
`Option SignedDyadicCode` du dernier résultat installé, read identité, événement
code et demandes de précision. Ce dernier résultat est nécessaire au read, même
s'il n'est pas lu par chaque transition. La banque, les archives, le journal et
les événements riches restent dans le contrat riche et sont oubliés seulement
dans sa projection numérique, autorisée par `kernelExact`/uniformité à précision
fixée. `nextExact`/`eventExact` comparent cette seule projection, jamais les banques.
La minimalité exacte est relative au contrat live complet et à cet environnement
fixé ; aucune minimalité riche ni physique n'est annoncée.

Le champ `Service.liveStep` capture seulement `kernels` et `modulus`. Son corps
obtient le `LiveEnvironment` du kernel, exécute `step` depuis sa mémoire initiale
explicitement projetée et lit `answer`. Il n'appelle ni `readout`, ni
`executeAt`/`executeReal`, ni le producteur riche. Les deux générateurs riche
et live sont des entrées séparées, reliées par une loi sur chaque Step courant.
`ofTerms` montre qu'aucune famille mathématique antérieure n'est exclue, mais
son générateur de commodité peut capturer `terms` : **aucune** garantie physique
sur les captures internes de ce callback n'en est déduite. Cette frontière
explicite est distincte des captures visibles de la fermeture du service,
contrôlées dans le C. Ni coût universel ni compacité d'un callback arbitraire.

**Vérifications de la correction constitutive.** Les trois modules production
`NativeLimitRuntime`, `NativeCauchy` et `EffectiveCorrespondence` comportent
respectivement 48, 22 et 20 déclarations explicites auditées ; leurs deux
fichiers de tests natif/terminal comportent 58 et 63 déclarations. La famille
test est composée de sommes ; sa loi consomme les quatre sous-Steps des deux
productions reçues. Les tests couvrent banque non initiale, plusieurs précisions,
continuation et retour à un indice conservé (sous l'inégalité des indices
explicitement reçue), source regroupée exacte, production installée partagée,
relecture sans regroupement, projections live exactes et comparaison numérique
aval à la limite-source. Le test terminal conserve les traces à plusieurs
requêtes et les trois successeurs. Le test natif compare maintenant le candidat
autoritatif `certified` à `addZeroCandidate`, de constructeur `add`. Sa convergence
consomme les sous-Steps limite et zéro possédés par l'addition reçue :
`observeLimit` s'applique au premier à précision `s+1`, et le second fournit
son `SameValue` avec zéro ; le seuil reste l'identité puisque `p ≤ s ≤ s+1`.
`candidateConstructorsDistinct` transforme leur égalité en `Empty` ;
`numericalAgreementWithoutIdentity` conserve conjointement cette séparation,
`Equivalent` et `NumericalFutureEquivalent`. `nativeUnique` et
`nativeAuthoritativeUnique` sont appliqués à ce candidat concret ; la trace
à deux requêtes utilise ses archives non initiales sans identifier les occurrences.
Le wrapper `certifiedCandidate` ne revendique plus une distinction syntaxique.
Le test leaf/certified de l'ancien lot d'unicité-source reste inchangé.

Les builds ciblés passent (161 jobs pour les deux tests et dépendances).
Le build global est rejoué, 398 jobs :
`ALL_CONSTANTS_OK constants=37002 modules=395 generatedExceptions=735 writtenExceptions=0`.
Les 396 fichiers Lean ont un unique audit terminal, aucun token interdit et
un olean ; les 329 modules production sont stratifiés sans orphelin.
Les quatre frontières d'import et leurs quatre autotests passent. Les 182
fixtures passent avec leurs 185 sites diagnostiques exacts et sans erreur supplémentaire.
Six nouvelles fixtures séparent kernels/terms, réception du contexte,
source/Step versus code, regroupement d'une source versus code reconstruit,
cible produite versus code prescrit et rétention du Step. Trois fixtures
existantes sont adaptées à la nouvelle archive exacte/à l'interface enrichie,
sans affaiblir leur refus de reset ou de loi numérique nue.

Les seize scripts codegen passent après stabilisation des artefacts. Le
contrôle natif suit cinq routes et rejette 40 mutations à classe de refus
vérifiée : production source et regroupement (callbacks concrets des Program),
charge normalisée issue du Step/Near exacts, mise à jour banque/journal et
installation partagée, fermeture live kernels+module seuls, convergence
extraite sans replay. Sont notamment rejetés l'oubli du contexte reçu, les
substitutions de Steps/archives, le reset de la banque, la capture visible du
family riche et la duplication valide d'une production/action. La boucle du
normaliseur générique existant reste une frontière nommée ; ses entrées et
la consommation de sa charge sont contrôlées. La continuation est interprétée
sur le chemin d'allocation partagé : aucun théorème sur la gestion C des
références ou sur l'allocation en place n'est prétendu. Les captures internes
des callbacks et les formations propositionnelles sont également exclues.

L'autotest des deux gates de fixtures passe les vingt cas : baselines Bash
et PowerShell de 182 fixtures chacune, puis dix-huit refus de mutations
d'inventaire, de source et de diagnostic/site. Il est exécuté sur les fixtures
figées, sans build concurrent ; aucun refus étranger au diagnostic attendu
n'est accepté. Le délai externe fixe de 180 secondes est remplacé par le budget
reproductible `60 + 90 × nombre de fixtures`, soit 16 440 secondes par façade
dans cet inventaire ; `--gate-timeout-seconds` permet un budget positif explicite.
Ce budget n'est ni une mesure de coût ni une borne de performance universelle.
La politique exacte des diagnostics et son délai interne de 90 secondes par
fixture sont inchangés. Un timeout externe est enregistré comme échec, jamais
comme refus Lean ; les mutations exigent le statut externe 1 et le diagnostic
de la politique, les baselines le statut 0 et l'inventaire complet sans doublon.
Des contrôles purs séparés vérifient les statuts interrompus et les deux
gestionnaires de timeout, y compris un message attendu précédant un timeout.
Les vingt résultats rejoués sont positifs, sans timeout, avec budget et durée
consignés dans les matériaux temporaires hors dépôt.
Les sept autotests documentaires et le contrôle séparé des liens, fences et
espaces finaux des quarante documents passent. Un premier contrôle des C/oleans
avait rencontré un artefact momentanément absent pendant le build ; le scan
et les seize contrôles sont relancés et passent après ce build, sans présenter
cette course d'artefacts comme un défaut scientifique.
Les gates `--static`, `--lean`, `verify.ps1` et `verify.sh` sont lancées et
restent chacune en échec, code 1 au premier `STALE_SOURCE:
GODEL_RELATIONAL_SEQUENTIAL_COMPLETENESS` préexistant. Le recalcul des
21 empreintes trouve seulement les deux stales préexistants, dont
`RUNTIME_EFFECTIVE_CAUCHY_REAL_CORRESPONDENCE` derrière ce premier arrêt.
Aucune empreinte du registre n'est rafraîchie. Ces scripts globaux ne sont
donc pas présentés comme verts ; leurs autres contrôles sont lancés séparément.

Les commandes comprennent les builds ciblés des modules concernés,
`lake build`, les seize `scripts/check-*-codegen.py`,
`scripts/check-expected-failures.ps1`,
`scripts/test-expected-failure-gates.py --output` vers un répertoire temporaire
hors dépôt, les contrôles d'import Python, les contrôles de stratification
PowerShell/Bash et leurs autotests, puis les contrôles documentaires et le
diff-check. Les matériaux bruts d'autotest demeurent hors du dépôt.

L'inventaire avant lot figeait 643 fichiers, dont le plan
`A9BE4D9A848B7B488F0BAFD9AC912836C3490F1D9D4DAD5F9E9FCED709A8B2C2`.
Les 31 anciens modules Reals et les treize tests `RelationalReal*` des lots
antérieurs au prototype natif restent octet-identiques. Leur inventaire
trié `chemin<TAB>SHA256<LF>` conserve
`0325B9801435A275605BEBC32F9AA42048451D889A5ADAD04345BABB355FD3F6`.
L'agrégation initiale ajoutait vingt et un fichiers. Sa correction ajoute un
module et six fixtures ; elle modifie les deux modules natif/terminal, le test
natif, son codegen, trois fixtures, les deux manifestes, les imports/audits publics
et ce plan. La forme de `NativeCauchyFamily` reçoit les kernels séparés et leur
raccord, dérivables pour toute ancienne donnée par `ofTerms`. La provenance,
les champs et signatures du prototype natif sont renforcés/remplacés pour porter
la source exacte, et non présentés comme inchangés. Les 44 anciens modules/tests
des lots antérieurs au prototype natif restent octet-identiques ; aucun ancien
constructeur `Real`, contrat ni énoncé de ces lots n'est modifié.
Le registre garde
`F16DDD58A37BCAAA9F9666D6ED688E5D4EDB14A1E435A4506BAC5A07E9E65C18`.
Passages canoniques/protégés, figures et statuts de revue restent inchangés.
La mise à jour d'une affirmation majeure et sa revue ne sont pas réalisées
par ce document de chantier. Aucun commit, push, fusion ou audit extérieur.

Ces six blocs exposent maintenant la production native riche et ses vues
numériques séparées. La correction est remise à la revue primaire avant
clôture des gates 4 (extension native) et 6 ; les builds et contrôles ci-dessus
ne constituent pas ce verdict scientifique. La gate 7 reste ouverte et aucun
travail de couverture des réels usuels n'est engagé ici.

### Gates terminales de preuve

Les critères successifs sont conservés ci-dessous. Les lots précédents et
les réalisations antérieures portent leurs résultats dans leurs portées
déclarées ; l'extension native de la gate 4 et la gate 6 sont en revue primaire
de la correction ci-dessus, tandis que la gate 7 reste ouverte. Une accumulation de
définitions ou un build vert ne remplace aucun de ces critères :

1. **Fermeture algébrique relationnelle.** Chaque opération construit un
   runtime fermé, conserve les ressources effectivement consommées et satisfait
   ses lois à équivalence comportementale près. Les constantes et opérations
   correspondantes sur les présentations restent des readouts aval.
2. **Corps ordonné constructif.** L'apartness est positive ; l'inverse exige un
   témoin d'apartness à zéro ; l'ordre est défini et manipulé sans décision
   globale cachée. Les compatibilités ordre–addition–multiplication sont
   prouvées sur les actions produites.
3. **Archimédianité et densité.** Les témoins dyadiques sont construits à partir
   de demandes finies et consommés dans les preuves. Une existence
   propositionnelle seule ne ferme pas cette gate.
4. **Complétude interne effective.** Une famille de Cauchy interne contient ses
   comportements, son module et ses exécutions. Le regroupement consomme leurs
   sorties, produit une cible limite, l'installe dans une mémoire et fournit le
   runtime limite. La cible ne figure pas dans la requête et n'est pas
   reconstruite depuis un readout extensif.
5. **Unicité et indépendance historique.** Deux productions limites de la même
   famille sont équivalentes quant à tous leurs futurs numériques, sans que
   leurs occurrences, archives ou journaux soient identifiés.
6. **Correspondance structurelle effective comportementale.** Pour la classe
   effective définie, le paquet terminal contient les deux applications, les
   deux allers-retours numériques, ainsi que la préservation et la réflexion
   des opérations, de l'apartness, de l'ordre, du comportement des familles et
   de leurs limites. Il ne constitue ni une égalité ni une isomorphie des
   familles riches et ne récupère pas par ce transport leurs témoins Cauchy,
   journaux ou histoires. Les preuves consomment les théorèmes constitutifs
   antérieurs ; elles ne redéfinissent pas des opérations extensives pour les
   réimporter. Les références canoniques en preuve et les appels compilés sont
   contrôlés séparément.
7. **Gate de couverture des réels usuels.** Il faut soit une identification
   directe, dans les deux sens et sous une équivalence explicite, avec la
   construction extensive retenue comme référence, soit un théorème de
   caractérisation et d'unicité dont toutes les hypothèses sont prouvées dans
   le dépôt. Cette gate enregistre séparément la portée effective et toute
   portée classique plus large.

### Critère terminal de succès et verdicts interdits

Le chantier pourra annoncer « correspondance avec les réels effectifs de la
construction choisie » après la gate 6, en nommant exactement la classe de
présentations couverte et l'équivalence comportementale/numérique retenue,
sans récupération des données riches oubliées par ce transport. Il ne pourra
annoncer « correspondance avec tous les réels usuels » qu'après la gate 7.
Avant cela, les verdicts autorisés seront
respectivement :

- addition relationnelle fermée ;
- structure de corps ordonné relationnel ;
- complétude de Cauchy effective ;
- correspondance structurelle effective comportementale ;
- couverture classique encore ouverte.

Il sera interdit de remplacer une gate manquante par un renommage, une
surjection de readout, une cardinalité, une propriété seulement propositionnelle
ou une équivalence qui oublie la direction de réalisation.

Pour chaque gate, les tests négatifs devront notamment empêcher :

- qu'une opération extensive soit utilisée pour définir son runtime ;
- qu'une limite préfabriquée soit placée dans la famille de Cauchy ;
- qu'un témoin d'ordre ou d'apartness soit obtenu par décision classique ;
- qu'un aller-retour numérique soit annoncé comme égalité des occurrences ;
- que la restauration du producteur et du module soit annoncée comme identité
  des familles, de leurs témoins Cauchy ou récupération de leurs histoires ;
- qu'une référence canonique propositionnelle soit confondue avec un appel
  compilé supplémentaire, ou que l'absence de celui-ci soit affirmée sans
  contrôle de la route compilée ;
- qu'une couverture des présentations effectives soit généralisée aux objets
  non reçus et non exécutables.

`AC` et `CH` ne font pas partie de ce cycle. Leur étude exigera ensuite une
théorie relationnelle explicite des collections, des fonctions de choix, des
parties et des comparaisons cardinales. Elles ne doivent pas être ajoutées aux
réels par simple extension de vocabulaire.
