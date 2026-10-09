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
n'est pas une coordonnée. La traduction de toutes les demandes entre deux
**états de couplage réexprimés différents** n'est pas encore construite ; le
raccord des descriptions de ressources ne suffit pas à transporter leur
disponibilité. Ne pas lire le contrat comme cette équivalence supplémentaire.

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

## Preuves et contrôles

| Passage | Source et déclarations |
| --- | --- |
| Disponibilité et diagnostic | [EncounterAdmissions](../../RelationalPerimeter/Relativity/Production/EncounterAdmissions.lean) : `CouplingFormation`, `decideEncounter`, `encounter_enabled`, `attach_refuses`, `consumed_refuses` |
| Production et sources | [ConstitutedEncounters](../../RelationalPerimeter/Relativity/Production/ConstitutedEncounters.lean) : `performEncounter`, `encounter_sources_distinct`, `encounter_first_effect_exact`, `encounter_consumes_occupancy`, `history_transport_append` |
| Présentations et transports | [LocalizedPresentations](../../RelationalPerimeter/Relativity/Reconstruction/LocalizedPresentations.lean) : `localized_location_exact`, `localized_return_location`, `localized_return_effects`, `localized_prolong_compose` |
| Accord consommé | [LocationAgreement](../../RelationalPerimeter/Relativity/Reconstruction/LocationAgreement.lean) : `producedLocationAgreement`, `LocationAgreement.site`, `continuedLocationAgreement` |
| Contrats et témoin fermé | [EncounterFutures](../../RelationalPerimeter/Relativity/Continuation/EncounterFutures.lean) : `all_futures_exact`, `head_independent`, `rich_futures_require_effects`, `Example.equal_archive_cannot_admit`, `Example.same_request_forbids_rich_grouping`, `Example.same_output_not_same_occurrence` |
| Client public | [EncounterChecks](../../Tests/Relativity/EncounterChecks.lean) : import de la seule racine publique |
| Partage compilé | [check-encounter-codegen.py](../../scripts/check-encounter-codegen.py) : producteurs nommés, helpers, branchements et absence de réexécution dans les transports de description |

Le contrôle compilé borne les appels aux producteurs nommés sur les chemins
locaux annoncés. Il ne mesure ni leur travail interne, ni le tas total, ni
un coût physique. Le runner partagé est `run`/`encounterThen` ; l'évaluateur
générique des contrats est une spécification à projections séparées.

## Ce qui reste ouvert

Cette construction fournit un premier accord **relatif à la loi de couplage
déclarée**. Elle ne clôt pas le lot physique complet : traductions de toutes
les demandes entre états de couplage réexprimés, réseau physique des passages
et raccord aux contraintes de reconstruction restent à construire.
La complétude des lecteurs localisants, la couverture continue, la dimension,
les cartes, la métrique, la courbure et les lois dynamiques R4-R7 restent
ouvertes. La cible finale n'est pas remplacée par ce modèle fini.

Les fondations, le maître, la machine et les anciens contrats ne sont pas
modifiés. Ce lot n'est pas présenté comme audité indépendamment. Son entrée
de registre avec évidence figée requiert d'abord une révision de référence
autorisée, conformément à la procédure scientifique.

Version anglaise : [Constituted encounter](constituted-encounter.en.md).
