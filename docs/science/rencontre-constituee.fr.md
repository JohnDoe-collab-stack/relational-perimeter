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

## Parcours mesurés et rencontres sur le même support

Le raccord productif ne repart plus d'un curseur antérieur à la rencontre.
[RecurringSignalJourneys](../../RelationalPerimeter/Relativity/Production/RecurringSignalJourneys.lean)
reconstruit l'origine émise et les relais utilisés depuis la formation enrichie.
Une comparaison ou une réception conserve cette ascendance ; un relais suivant
la prolonge. Le témoin `RecurringUnitJourney` justifie séparément l'incrément
de chaque relais. L'entrée depuis un curseur ancien consomme sa formation,
sans rejouer ses producteurs. `RecurringRelativeReading` retrouve la lecture
relative antérieure et conserve son origine et ses comptes par transport.

[EncounterRelativePaths](../../RelationalPerimeter/Relativity/Production/EncounterRelativePaths.lean)
porte les deux parcours sur l'état de couplage reçu. `measure` livre leurs deux
signaux respectifs, forme la disponibilité puis produit la rencontre admise.
Il ne substitue pas la livraison répétée d'un seul record à ces deux parcours.
La lecture relative utilise la première arrivée, l'origine commune constituée
et le nombre positif de relais du parcours d'échelle. La réponse brute de
l'interaction reste la différence entre les deux arrivées : ces deux lectures
ne sont pas confondues.

`refine` poursuit les deux parcours depuis leurs propres extrémités, avec la
calibration reçue. Pour les comptes `a` et `b`, la demande basse produit
`a+a` et `b+b` ; la demande haute produit `a+a+1` et `b+b`. Les nouveaux
relais sont exécutés, puis leurs deux arrivées sont livrées et consommées.
`Measurement.next` conserve le successeur de cette rencontre entière,
ports vidés inclus. `runMeasurements` reprend ce résultat pour toute liste
finie de demandes ; `measurement_runs_append` raccorde les paquets entiers.
La tête locale ne reçoit pas le suffixe futur. Ce programme est défini sur
un couplage local ; le programme du réseau fini demeure inchangé.

[MeasuredEncounterDescriptions](../../RelationalPerimeter/Relativity/Reconstruction/MeasuredEncounterDescriptions.lean)
consomme les mêmes rencontres enregistrées dans `LocationAgreement` et les
contraintes d'ancre existantes. La lecture relative est raccordée au premier
effet effectivement enregistré. Les effets des deux parcours restent
séparément accessibles après toute histoire locale.
[MeasuredEncounterFutures](../../RelationalPerimeter/Relativity/Continuation/MeasuredEncounterFutures.lean)
réemploie le contrat riche antérieur sans le restreindre : lorsque les records
diffèrent, la même demande `attachedEffects` interdit leur regroupement riche,
après toute liste finie de demandes du contrat principal, refus compris.

Le [client public](../../Tests/Relativity/MeasuredPathChecks.lean) réalise
les comptes un/deux, une lecture relative un demi et une réponse brute un.
Une demande haute produit trois/quatre et la lecture trois quarts ; une
reprise basse poursuit le successeur produit. Leurs origines et les effets
de la première rencontre subsistent. Les évaluations sont des smoke checks
d'exécutabilité, non des expériences physiques ou des mesures de complexité.
Les contrôles négatifs refusent l'ancien support, l'admission consommée
et le transfert abusif des effets entre participants.

Les lois de calibration, de couplage et les demandes de subdivision sont
déclarées, non découvertes par ce lot. Le raccord ferme P1-P2 pour ces parcours
locaux calibrés ; il ne construit encore ni une localisation continue, ni
un raccord physique entre rencontres distinctes, ni une couverture du domaine.
Les anciennes contraintes d'ancre sont consommées, mais la génération des
contraintes localisantes de P3-P5 reste à établir.

## Contraintes de mesure et conservation de la détermination décrite

Une nouvelle rencontre mesure de nouveaux parcours. Elle n'est pas un autre
nom de la rencontre précédente. La demande haute change par exemple le rapport
un demi en trois quarts. Utiliser directement cette nouvelle valeur comme une
lecture plus précise de l'ancienne serait faux.

[EncounterMeasurementLaws](../../RelationalPerimeter/Relativity/Production/EncounterMeasurementLaws.lean)
prouve depuis les comptes effectivement produits que le rapport suivant est
le rapport précédent plus `extra/(b+b)`, où `b` est le nombre de relais du
parcours d'échelle reçu et `extra` est zéro ou un selon la demande. Cette loi
est une conséquence de la calibration et de la subdivision déclarées. Pour
toute chaîne finie, son changement cumulé est extrait des étapes enregistrées.
Soustraire ce changement à la lecture finale retrouve exactement la lecture
initiale. Les nouvelles occurrences de rencontre restent distinctes de toutes
les références anciennes transportées.

[MeasuredPathConstraints](../../RelationalPerimeter/Relativity/Reconstruction/MeasuredPathConstraints.lean)
fixe la mesure d'origine dans le type de chaque contrainte. Son lecteur utilise
l'effet attaché, l'origine transportée et l'échelle de cette mesure exacte.
La certification d'une fenêtre reçue retourne un témoin ou un refus justifié.
Une reprise produit une seule étape de mesure, lit son effet enregistré,
soustrait le changement cumulé justifié et construit une fenêtre fine sur
la **détermination ancienne**. Son intersection avec la fenêtre reçue rend
exactement la contrainte antérieure, transportée sur le successeur réel.

Toute liste finie de demandes préserve cette détermination et satisfait
toutes les précisions demandées. La reprise reçoit le paquet retourné entier ;
elle est égale à la course concaténée. Deux descriptions du même résultat de
mesure ont une contrainte commune construite avec ses deux restrictions et
ses deux bornes. Leurs histoires positives justifient qu'elles décrivent cette
même détermination ; l'égalité des nombres de deux mesures étrangères ne suffit
pas. Ce raccord descriptif n'assemble pas leurs futurs distincts : il garde
le support courant de la première et y transporte la description de l'ancien
résultat portée par la seconde.

Dans le [client public](../../Tests/Relativity/MeasuredConstraintChecks.lean),
les parcours finaux ont les comptes six/huit après deux demandes, mais la
contrainte décrit toujours le rapport initial un demi. Les garanties sont
prouvées pour toute liste finie, pas seulement pour ce smoke check. Le contrat
riche entier continue à séparer les effets des deux participants après les
mesures et après toutes les demandes ultérieures, refus compris.

Ce lot ferme le raccord **descriptif local** de P3 : mesure, détermination
suivie, précision, restrictions et reprise partagent leurs ressources exactes.
La précision borne la fenêtre de description d'une lecture rationnelle déjà
exacte ; elle ne mesure pas une incertitude physique ni une information inconnue
que les nouvelles rencontres auraient découverte. Ce résultat fournit à P4
des contraintes et l'accord sur la rencontre ancienne. Il ne justifie pas un
accord de localisation entre rencontres différentes, ne fusionne aucune source
et ne construit pas encore le domaine relativiste.

## Regroupement vérifié des descriptions mesurées

[MeasuredLocationGrouping](../../RelationalPerimeter/Relativity/Reconstruction/MeasuredLocationGrouping.lean)
construit une description commune pour deux descriptions mesurées reçues sur
le même support courant. Chacune porte sa mesure, son histoire positive, son
participant et sa contrainte de P3. Le contrôleur lit les références exactes
de la rencontre, du signal numérateur et de l'origine, ainsi que l'échelle
positive issue du parcours mesuré. Il ne compare ni les valeurs numériques
seules ni le recoupement des fenêtres. Les positions servent à reconnaître
les références typées sur ce support ; elles ne sont pas des coordonnées.

Les lecteurs préservés sont fixés avant le contrôle : la lecture d'interaction
et la lecture relative commune aux parcours de la mesure. Une autorisation
acceptée permet de construire la description commune, avec une preuve séparée
de préservation. Son action consomme cette autorisation. La fenêtre commune
est l'intersection des contraintes reçues ; ses restrictions rendent exactement
les deux **descriptions projetées**, références comprises. Elles ne reconstruisent
pas les participants ni leurs traces depuis la cible commune. Tous les lecteurs
sélectionnés factorisent par celle-ci.

Le consommateur des courses de P3 passe effectivement par ce contrôleur.
Après toute liste finie de demandes de précision, la description regroupée
conserve toutes les bornes demandées. Une histoire de continuation réelle
transporte ses références et conserve ces lectures. Ce transport commute
avec la restriction ; il ne peut pas rendre égales deux signatures auparavant
distinctes. Ces demandes de lecture ne nécessitent aucune nouvelle disponibilité
de ports et n'admettent pas une nouvelle rencontre à partir de l'ancienne.

Le [client public](../../Tests/Relativity/MeasuredLocationGroupingChecks.lean)
prouve deux cas complémentaires : les deux descriptions des participants
d'une même mesure sont acceptées ; une nouvelle mesure des mêmes parcours
a la même lecture relative mais une autre référence de rencontre et reste
refusée. Le contrôle est donc plus exigeant que l'égalité des nombres.
Il s'agit d'une règle **suffisante et conservatrice**, pas d'une caractérisation
de toutes les descriptions physiquement équivalentes.

La description commune ne remplace pas l'état vivant ni les records des
participants. Ceux-ci restent des sources distinctes. Sous le contrat riche
inchangé, la même demande `attachedEffects` peut encore distinguer leurs
effets, même si leurs lecteurs sélectionnés factorisent. Aucun oubli de
mémoire ni regroupement de ces futurs riches n'est revendiqué.

Ce passage réalise un regroupement local relatif aux lois instrumentales
et aux références constituées déjà disponibles. Il ne transforme pas la
référence d'une rencontre en point idéal et ne décide pas si des rencontres
distinctes occupent le même lieu physique. P4 reste ouvert sur cette loi
localisante supplémentaire et sa réalisation ; P5-R7 ne sont pas fermés
par cette reconnaissance d'occurrences.

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
| Ascendance sur le support enrichi | [RecurringSignalJourneys](../../RelationalPerimeter/Relativity/Production/RecurringSignalJourneys.lean) et [RecurringRelativeReadings](../../RelationalPerimeter/Relativity/Production/RecurringRelativeReadings.lean) : `recurringJourney`, `RecurringUnitJourney.reading_exact`, `RecurringJourney.transport_origin`, `recurring_lift_reads_same_ratio` |
| Mesures et reprises partagées | [EncounterRelativePaths](../../RelationalPerimeter/Relativity/Production/EncounterRelativePaths.lean) : `measure`, `refine`, `measurement_raw_output`, `refinement_counts`, `measurement_runs_append`, `measurement_chain_keeps_sources` |
| Consommateurs des records mesurés | [MeasuredEncounterDescriptions](../../RelationalPerimeter/Relativity/Reconstruction/MeasuredEncounterDescriptions.lean) et [MeasuredEncounterFutures](../../RelationalPerimeter/Relativity/Continuation/MeasuredEncounterFutures.lean) : `measured_ratio_reads_consumed_effect`, `measured_encounter_keeps_effects`, `measured_requests_preserve_path_distinctions` |
| Client des reprises | [MeasuredPathChecks](../../Tests/Relativity/MeasuredPathChecks.lean) : lectures différentes, reprise sur le successeur, composition et contrat riche |
| Changement de lecture justifié | [EncounterMeasurementLaws](../../RelationalPerimeter/Relativity/Production/EncounterMeasurementLaws.lean) : `refinement_affine_reading`, `measurement_chain_returns_original_reading`, `refined_encounter_is_not_an_old_occurrence` |
| Contraintes de la détermination suivie | [MeasuredPathConstraints](../../RelationalPerimeter/Relativity/Reconstruction/MeasuredPathConstraints.lean) : `measured_path_value_persists`, `corrected_refinement_reads_old_determination`, `measured_description_run_returns_exactly`, `measured_description_bounds_every_request`, `common_measured_descriptions_return_both` |
| Client des contraintes et futurs | [MeasuredConstraintChecks](../../Tests/Relativity/MeasuredConstraintChecks.lean) et [MeasuredEncounterFutures](../../RelationalPerimeter/Relativity/Continuation/MeasuredEncounterFutures.lean) : `every_requested_precision_is_met`, `measured_description_futures_keep_distinctions` |
| Autorisation et description commune locales | [MeasuredLocationGrouping](../../RelationalPerimeter/Relativity/Reconstruction/MeasuredLocationGrouping.lean) : `measured_grouping_decision_exact`, `grouped_measured_reader_factorization`, `grouped_measured_locations_return_both`, `measured_signature_readers_prolong`, `grouped_measured_description_every_precision` |
| Égalité numérique insuffisante et contrat riche inchangé | [MeasuredLocationGroupingChecks](../../Tests/Relativity/MeasuredLocationGroupingChecks.lean) : `repeated_measurement_has_same_relative_value`, `repeated_measurement_still_refuses_grouping` ; [MeasuredEncounterFutures](../../RelationalPerimeter/Relativity/Continuation/MeasuredEncounterFutures.lean) : `grouped_measured_description_is_not_rich_equivalence` |

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

[check-measured-encounter-codegen.py](../../scripts/check-measured-encounter-codegen.py)
contrôle les sites d'appel nommés du raccord mesuré : deux livraisons et une
interaction par tête, deux courses de relais puis une mesure par raffinement,
une reprise par nœud et la boucle sur l'état retourné. Il vérifie séparément
le graphe statique sans producteurs des consommateurs. Pour les contraintes,
il vérifie un appel au raffinement par étape, la consommation de son effet
enregistré et la reprise du paquet retourné ; la description et le changement
cumulé ne rappellent pas les producteurs nommés. Comme le contrôle du
réseau, il ne borne pas la multiplicité à travers des callbacks arbitraires,
le travail interne d'une course de relais, le coût total ou la géométrie.
Il vérifie aussi un site de reconnaissance et un site de construction de la
description commune dans le contrôleur, un appel de ce contrôleur par le
consommateur des courses, et l'absence de producteurs nommés dans leurs
graphes statiques. Cela ne remplace pas les preuves de préservation des lecteurs.

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
