# Rencontre constituée : admission, localisation locale et effets de parcours

Deux réceptions conservées dans une histoire ne suffisent pas à autoriser
une nouvelle interaction. Le modèle local ajouté distingue cette archive
de la disponibilité présente : deux ports doivent avoir reçu leurs données,
puis l'interaction consomme leur disponibilité. Elle produit une nouvelle
occurrence, sans remplacer les deux occurrences d'arrivée.

Depuis cette production, les deux participants décrivent la même rencontre.
Cet accord n'identifie pas leurs sources ni leurs parcours. Dans le cas
construit, leurs lectures numériques sont égales, mais un parcours contient
deux incréments et l'autre aucun. Une demande identique de lecture des effets
attachés distingue encore leurs descriptions, après toute continuation finie.

## Loi déclarée et portée

### Assemblage fini de couplages

Le lot réseau déclare un assemblage de plusieurs couplages à ports propres,
sur le même préfixe de ressources constitué reçu. Chaque attachement choisit
une référence de calibration réellement disponible ; deux attachements peuvent
partager cette calibration. Leur indépendance d'occupation est la loi idéale
d'assemblage explicitement ajoutée, pas une conséquence des valeurs de leurs
lectures ni une preuve de séparation spatiale. Un indice de cellule désigne
l'attachement sélectionné, jamais une coordonnée.

[CouplingNetworks](../../RelationalPerimeter/Relativity/Production/CouplingNetworks.lean)
forme positivement l'assemblage et chacune de ses transitions. Une livraison
exige un port vacant de la cellule choisie. Une interaction consomme ses deux
ports ; les autres cellules transportent leurs propres réceptions à travers
la même production de ressources. Leur admission déjà constituée reste
disponible. Une archive ne fournit aucune admission actuelle.

[NetworkEncounterPassages](../../RelationalPerimeter/Relativity/Production/NetworkEncounterPassages.lean)
lie quatre productions : émission depuis la sortie d'une rencontre, deux
livraisons dans une cellule effectivement vide, puis interaction admise dans
cette cellule. Les chemins de dépendance utilisent les ports de ces productions
stockées. Le premier record à destination est prouvé égal à l'émission de
la sortie effectivement produite à l'origine et du payload reçu. Les
reprises finies consomment le dernier résultat, le payload
transporté et la vacance conservée ; leur concaténation retrouve exactement
la même course. Les trois suffixes locaux fermés émettent la sortie, reçoivent
le premier record ou le relaient avec la calibration attachée. La tête entière
reste identique entre ces suffixes réellement exécutés ; aucun callback ou
futur achevé n'entre dans le producteur.

[NetworkEncounterDescriptions](../../RelationalPerimeter/Relativity/Reconstruction/NetworkEncounterDescriptions.lean)
consomme les interactions admises du réseau dans les accords d'attachement
et contraintes d'ancre existants. Les occurrences de réception restent
distinctes, les deux effets restent lisibles, et le passage ne confond pas
les occurrences de ses rencontres. Cet assemblage n'ajoute ni vitesse,
distance, voisinage physique ni point continu. R4.2.2 et la couverture physique
de R4.3 restent ouverts ; les anciens contrats ne sont pas remplacés par ces
trois suffixes ou par les courses de routage.

Le [contrôle du C généré](../../scripts/check-network-encounters-codegen.py)
vérifie les sites nommés de partage, la reprise compilée et l'absence de
producteurs statiquement accessibles depuis les consommateurs descriptifs.
Il ne démontre ni coût total ni validation empirique de la loi d'assemblage.

### Couplage local initial

Il s'agit d'un **modèle idéal de couplage local à deux ports avec rétention**.
L'instrument est attaché à une occurrence de calibration dans le préfixe
constitué effectivement reçu. Une livraison lit une référence de signal
présente sur ce support et produit une réception sur un port vacant. Le
premier port conserve cette réception jusqu'à la consommation conjointe.
Les autres opérations de signal la transportent. Un port déjà occupé refuse
une livraison ; une interaction sans les deux ports occupés est refusée.

Cette loi est une entrée déclarée du modèle, pas une découverte ni une loi
empiriquement validée. Les signaux sont des **records locaux réutilisables**,
non des particules linéaires dont toute copie serait interdite. Une nouvelle
livraison depuis un ancien record produit une nouvelle réception ; elle ne
réautorise pas la consommation de l'ancienne réception. Aucune vitesse de
propagation, distance, métrique, simultanéité globale ou coordonnée n'entre
dans l'admission.

La lecture numérique de l'interaction réemploie la comparaison calibrée
existante. Ce qui la distingue d'une comparaison d'archives est sa formation
par les livraisons et sa consommation des ports. Les ports sont ceux de cette
loi locale ; ils ne constituent pas encore un réseau de lieux physiques.

## Chaîne effectivement construite

```text
préfixe et calibration constitués reçus
  -> formation de la disponibilité par les livraisons
  -> diagnostic d'admission positive ou refus
  -> une production conjointe et son successeur
  -> deux présentations de cette rencontre produite
  -> LocationAgreement et occurrence locale commune
  -> reprises depuis le successeur et lectures des effets attachés
```

`CouplingFormation` est obligatoire dans `State`. Ses transitions portent
les productions de réception réellement exécutées. `EncounterAdmission`
reconstruit les deux arrivées de la phase disponible ; il ne reçoit pas
`LocationAgreement`. `performEncounter` produit la comparaison depuis ces
références. `afterEncounter` utilise cette même production et vide les ports.

`LocalizedPresentation` sélectionne un participant de cette production et
un chemin de description constitué. Son occurrence localisante est celle
de l'interaction exécutée, pas un point donné ni une réponse numérique
constante. `producedLocationAgreement` raccorde les deux participations à
cette rencontre précise. Le consommateur `LocationAgreement.site` porte
leurs références par un raccord exact. Cet objet n'est **pas encore une
localisation du continuum relativiste**.

Les changements exacts de description ont des lois de retour pour l'occurrence
et les effets. Leur composition exige une présentation intermédiaire
commune. Les prolongements suivent les productions stockées ; ils préservent
la même rencontre passée, sans imposer que tous les événements futurs de ses
participants soient colocalisés. Deux nouvelles interactions sur le même
instrument restent deux occurrences distinctes, même avec la même réponse.

## Contrats et séparation observable

`contract` permet toute liste finie d'émissions, relais, réceptions,
inspections typées, livraisons et interactions, y compris les refus.
`run` lie une réponse par demande puis reprend depuis son état produit.
`all_futures_exact` et `final_state_exact` raccordent ce runner à la
spécification ; `run_append_state` et `history_transport_append` raccordent
les reprises et leurs références.

Les inspections anciennes sont traduites par les références du prolongement,
avec `transported_inspection_exact`. Leur numéro local peut changer : il
n'est pas une coordonnée. `StateRaccord` porte aussi l'instrument et la phase
d'occupation exacte, sur deux états déjà positivement formés. Il traduit
toute la grammaire entre ces descriptions : actions locales, livraisons,
interactions et inspections. Les admissions et les refus sont préservés.
Après une production, le raccord évolue avec les deux successeurs réels.
`runSharedCoupling` produit une réponse du côté source puis transporte son
rôle et sa sortie stockés vers l'autre présentation. `transported_all_futures`
prouve l'exactitude pour toute liste finie, sans filtrer les refus. Le client
fermé échange deux déterminations déjà produites, sans les exécuter à nouveau,
puis montre que figer la permutation d'adresses initiale briserait le contrat.

`readerContract` fixe séparément les lectures d'une description riche.
La demande `attachedEffects` est identique pour les deux participants ; son
interprétation lit leur occurrence attachée propre. `rich_futures_require_effects`
montre que deux descriptions équivalentes sous ce contrat ont les mêmes
effets. Le cas fermé `Example.same_request_forbids_rich_grouping` réfute cette
équivalence pour les deux parcours, après n'importe quelle suite de demandes
du contrat principal. Ce n'est pas seulement la comparaison de deux listes
de requêtes aux adresses différentes.

Ces contrats sont locaux. Ils ne remplacent ni le contrat du maître ni le
contrat physique complet à construire. Aucun oubli mémoire n'est autorisé
par le seul accord localisant.

## Passages entre rencontres et contraintes

Une rencontre suivante n'est pas reliée causalement à la précédente par sa
seule position dans une histoire. `producePassageHeads` lie une émission
depuis la sortie de la rencontre précédente, deux nouvelles livraisons du
record émis, puis leur interaction admise. `produceLinkedEncounter` consomme
ce paquet stocké et construit un chemin positif de ports utilisés jusqu'à
la nouvelle occurrence. Les deux réceptions sont distinctes, même lorsqu'elles
lisent le même record. `PassageCourse` compose ces liens et leurs histoires
sur les successeurs effectivement produits. Son prolongement exécutable
accepte toute longueur finie ; aucun horizon futur n'est reçu par le producteur
d'un lien. `PassageCourse.used` fournit la dépendance positive des extrémités
pour toute course non vide.

Le chemin utilisé prouve que ces occurrences sont distinctes. Chaque rencontre
possède son propre accord local entre ses participants. L'accord de l'ancienne
rencontre est transporté, avec les effets attachés, mais n'est pas étendu en
un accord identifiant les deux extrémités du passage. Dans le cas fermé,
leurs valeurs numériques sont pourtant égales. Il s'agit d'une course causale
sur un instrument constitué, pas encore d'un réseau de plusieurs instruments
physiques, d'une distance ou d'une loi de propagation.

`EncounterReadingConstraints` raccorde maintenant ces présentations aux
contraintes et recouvrements finis existants. Un accord de rencontre transporte
les clauses portant sur sa lecture d'interaction effective, puis un recouvrement
sélectionne ses feuilles depuis les certificats transportés. Les restrictions
rendent les lectures d'entrée, et le raffinement ne supprime aucun effet
attaché. Les clauses riches suivent une réexpression exacte du même participant
ou l'histoire de continuation ; elles ne passent pas d'un participant à l'autre
par le seul accord localisant. Le test négatif correspondant refuse cette
substitution. Ces recouvrements restent des recouvrements de lectures, non
des voisinages physiques ni une couverture du domaine relativiste.

## Précision des rencontres et portée de la couverture

[EncounterPrecisionDescriptions](../../RelationalPerimeter/Relativity/Reconstruction/EncounterPrecisionDescriptions.lean)
raffine les contraintes d'interaction d'une rencontre déjà constituée. Chaque
étape consomme les valeurs certifiées reçues, calcule ses fenêtres fines et
produit leurs restrictions positives. Pour toute liste finie de demandes,
les fenêtres finales respectent toutes les précisions demandées, gardent
les valeurs initiales et rendent exactement les certificats d'entrée.
La reprise reçoit le résultat produit ; elle est prouvée égale à la course
concaténée. Le transport par `LocationAgreement` commute avec une étape et
avec la course entière. Deux courses ont un raffinement commun construit
qui rend leurs deux certificats et conserve leurs deux bornes.
Il ne transporte pas les effets d'arrivée entre
participants. Cela réalise la partie descriptive de R4.2 sur les rencontres
existantes, pas la génération de localisations au-delà des événements exécutés.

[EncounterReadoutBasis](../../RelationalPerimeter/Relativity/Reconstruction/EncounterReadoutBasis.lean)
interprète une base de fenêtres strictement ouvertes sur ces présentations.
Toute présentation a un voisinage de lecture positivement réalisé à chaque
précision. Deux réalisations produisent leur intersection finie ; un
recouvrement positif sélectionne ses feuilles avec retour exact du certificat.
Deux lectures différentes ont un séparateur positif. L'accord de **tous**
les voisinages caractérise exactement l'égalité des lectures d'interaction.

Le [client fermé](../../Tests/Relativity/EncounterPrecisionChecks.lean) fixe
aussi la limite : deux rencontres reliées par un passage utilisé ont la même
lecture, restent des occurrences distinctes, et ont pourtant les mêmes
admissions pour tous ces voisinages. Un autre parcours produit une lecture
différente effectivement séparée. La base n'est donc ni constante ni un
reconnaisseur des occurrences. Elle ne décide pas si les rencontres occupent
des localisations physiques identiques ou différentes.

Les réalisations localisantes compatibles de R4.2.2, leurs raccords physiques,
les séparateurs de localisation et la couverture par des points construits
de R4.3 restent ouverts. Une base de lectures n'est pas une topologie physique
reconstruite. Les fenêtres à précision arbitraire spécifient des possibilités
de lecture ; un run fini n'a pas exécuté une infinité de mesures.

## Preuves et contrôles

| Passage | Source et déclarations |
| --- | --- |
| Disponibilité et diagnostic | [EncounterAdmissions](../../RelationalPerimeter/Relativity/Production/EncounterAdmissions.lean) : `CouplingFormation`, `decideEncounter`, `encounter_enabled`, `attach_refuses`, `consumed_refuses` |
| Production et sources | [ConstitutedEncounters](../../RelationalPerimeter/Relativity/Production/ConstitutedEncounters.lean) : `performEncounter`, `encounter_sources_distinct`, `encounter_first_effect_exact`, `encounter_consumes_occupancy`, `history_transport_append` |
| Présentations et transports | [LocalizedPresentations](../../RelationalPerimeter/Relativity/Reconstruction/LocalizedPresentations.lean) : `localized_location_exact`, `localized_return_location`, `localized_return_effects`, `localized_prolong_compose` |
| Accord consommé | [LocationAgreement](../../RelationalPerimeter/Relativity/Reconstruction/LocationAgreement.lean) : `producedLocationAgreement`, `LocationAgreement.site`, `continuedLocationAgreement` |
| Contrats et témoin fermé | [EncounterFutures](../../RelationalPerimeter/Relativity/Continuation/EncounterFutures.lean) : `all_futures_exact`, `head_independent`, `rich_futures_require_effects`, `Example.equal_archive_cannot_admit`, `Example.same_request_forbids_rich_grouping`, `Example.same_output_not_same_occurrence` |
| Client public | [EncounterChecks](../../Tests/Relativity/EncounterChecks.lean) : import de la seule racine publique |
| Contrat entièrement traduit | [CouplingDescriptions](../../RelationalPerimeter/Relativity/Production/CouplingDescriptions.lean) et [TransportedEncounterFutures](../../RelationalPerimeter/Relativity/Continuation/TransportedEncounterFutures.lean) : `StateRaccord`, `transported_admission_exact`, `shared_run_source_exact`, `shared_run_target_exact`, `transported_all_futures`, `continued_full_contract_exact` |
| Passages utilisés et accords distincts | [EncounterPassages](../../RelationalPerimeter/Relativity/Production/EncounterPassages.lean) et [LinkedEncounterLocations](../../RelationalPerimeter/Relativity/Reconstruction/LinkedEncounterLocations.lean) : `producePassageHeads`, `produceLinkedEncounter`, `PassageCourse.used`, `passage_does_not_identify_locations`, `nonempty_course_keeps_distinct_locations` |
| Contraintes consommées | [EncounterReadingConstraints](../../RelationalPerimeter/Relativity/Reconstruction/EncounterReadingConstraints.lean) : `transportConstraints`, `location_constraints_agree`, `selectCover`, `located_cover_uses_recorded_values`, `located_constraints_prolong` |
| Clients du raccord complet | [TransportedEncounterChecks](../../Tests/Relativity/TransportedEncounterChecks.lean) et [LocatedEncounterChecks](../../Tests/Relativity/LocatedEncounterChecks.lean) : permutation non identitaire, contrat complet et course arbitraire |
| Partage compilé | [check-encounter-codegen.py](../../scripts/check-encounter-codegen.py) : producteurs nommés, helpers, branchements et absence de réexécution dans les transports de description |

Le contrôle compilé borne les appels aux producteurs nommés sur les chemins
locaux annoncés. Il ne mesure ni leur travail interne, ni le tas total, ni
un coût physique. Le runner partagé est `run`/`encounterThen` ; l'évaluateur
générique des contrats est une spécification à projections séparées.
Le contrôle inclut la réponse partagée entre présentations et les quatre
producteurs du paquet de passage : une émission, deux livraisons et une
interaction. Il distingue ce paquet de son consommateur descriptif et vérifie
l'absence de producteur statiquement accessible hors de cette frontière.
Il ne mesure pas le coût des témoins de formation ni celui des transports.

[check-encounter-descriptions-codegen.py](../../scripts/check-encounter-descriptions-codegen.py)
contrôle séparément les nouveaux consommateurs : un site d'appel nommé
pour la tête, la récursion et leur composition dans le runner, et aucun
producteur accessible dans les graphes statiques des raffinements, reprises,
transports, intersections et sélections. Les cibles de fermetures statiquement
connues sont suivies. Ce n'est pas une preuve sur des callbacks arbitraires,
un coût total ou une topologie physique.

## Ce qui reste ouvert

Cette construction fournit un premier accord **relatif à la loi de couplage
déclarée**. Elle ne clôt pas le lot physique complet : traductions de toutes
les demandes du contrat local et raccord aux contraintes de lectures sont
maintenant construits, ainsi qu'une course causale de rencontres. Restent
à établir les lois d'un réseau physique, les consommateurs localisants et
la justification physique des recouvrements de reconstruction.
La complétude des lecteurs localisants, la couverture continue, la dimension,
les cartes, la métrique, la courbure et les lois dynamiques R4-R7 restent
ouvertes. La cible finale n'est pas remplacée par ce modèle fini.

Les fondations, le maître, la machine et les anciens contrats ne sont pas
modifiés. Ce lot n'est pas présenté comme audité indépendamment. Son entrée
de registre avec évidence figée requiert d'abord une révision de référence
autorisée, conformément à la procédure scientifique.

Version anglaise : [Constituted encounter](constituted-encounter.en.md).
