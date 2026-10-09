# Rapport d'auteur — tranche 3B

## Résultat transmis

`FormationTransport.lean.in` contient 28 déclarations auditées. `FormationTransportExamples.lean.in` en contient 33. Les deux sources finales ont compilé sous le Lean épinglé du dépôt, et les 61 audits finaux ne dépendent d'aucun axiome.

Le premier fichier a été compilé contre les interfaces canoniques `SignatureTransport.lean` et `SpineTransport.lean` du coordinateur. Le coordinateur l'a ensuite intégré et compilé sous `RelationalPerimeter/Constitution/FormationTransport.lean`. Le second fichier a été compilé en important ce module canonique intégré. Les sorties finales sont `formation-transport.log` et `formation-models.log`.

## Hypothèses réellement consommées

La construction reçoit une formation positive `F`, une signature cible et un `ConstitutiveSignatureTransport F.signature target`. Elle reconstruit `F.transport change` :

- les types `State` et `Step` restent identiques, avec tous les champs de chaque pas ;
- chaque nœud est l'application construite `change.mapNode` ;
- la lecture de compatibilité de chaque pas est l'image de sa lecture initiale dans la fibre correspondante.

Les identités des états et des pas sont visibles par réduction. Le déploiement commutant est démontré par induction et ne constitue pas un champ supposé d'un nouvel objet. La signature entière sert au transport des nœuds et de chaque lecture de pas.

## Obligations satisfaites

`PositiveHistory.transportSignature` et `restoreSignature` reconstruisent récursivement les histoires. Leurs deux retours donnent `signatureTransport`, un transport exact des histoires entières à extrémités fixes. `transport_append` prouve la commutation avec la composition ; `transport_deploy` prouve l'égalité entre l'épine déployée après reconstruction et `change.mapSpine` de l'épine originale.

Les occurrences ont également leurs deux applications récursives et leurs deux retours (`occurrenceSignatureTransport`). `transport_position` raccorde leur lecture aux positions du transport d'épines, avec le transport explicite le long de `transport_deploy`. Quatre lemmes de réindexation des positions et relations exposent les casts nécessaires. `transport_precedes_iff` et `transport_next_iff` prouvent la conservation et la réflexion de la précédence et de la succession immédiate aux positions lues. `transport_link` conserve exactement la lecture du nœud source, du nœud cible et du témoin de compatibilité d'un pas.

Une continuation choisie se reconstruit avec le même successeur et le même pas entier. `transport_walk` prouve la commutation de sa marche finie, y compris son extrémité et son histoire. Ce résultat ne construit aucun choix de successeur supplémentaire.

## Modèles

Le modèle utilise les états `Unit`, les pas `Bool × Bool` et une lecture de compatibilité donnée par la première coordonnée. L'échange de `Bool` dans toutes les fibres de compatibilité et de provenance modifie effectivement les lectures, sans modifier la seconde coordonnée du pas.

Deux histoires munies respectivement des pas `(true, false)` et `(true, true)` ont le même déploiement et des données de pas distinctes. La reconstruction de signature conserve ces données entières et son retour retrouve l'histoire originale. Ce modèle distingue donc le transport exact des histoires construites du seul déploiement, qui continue à oublier des données supplémentaires d'un pas.

Une histoire de trois pas porte trois occurrences sur des nœuds bruts identiques. Après transport, la première position succède immédiatement vers la deuxième, précède la troisième, et reste distincte de celle-ci. Les accords de composition, déploiement et marche choisie sont aussi instanciés.

## Limites

Il s'agit d'un changement de signature vers une formation explicitement reconstruite. Il ne fournit pas un transport exact vers une formation cible arbitraire déjà donnée. Une telle extension demanderait des accords pour ses états, nœuds, types de pas et lectures dépendantes ; une simple application entre états ou pas ne suffit pas à annoncer une inverse.

Les inverses d'histoires et d'occurrences ne constituent pas une reconstruction générale des données d'une épine cible. Les fonctions de pôles, l'obstruction historique, la rigidité des réalisations et une classification des rôles ne sont pas annoncées ici. Le raccord des fibres fermantes et des données sélectionnées est développé séparément par le coordinateur.

Les brouillons, sondes et sorties de travail restent dans ce répertoire. Les fichiers `ApiFixture.lean.in`, `UniverseProbe.lean.in`, `RecursorProbe.lean.in` et `CompileUnit.lean.in` sont des instruments de développement, sans statut de résultat. Les deux sources finales nommées en tête et leurs logs font foi pour le présent rapport. Une revue indépendante reste nécessaire avant l'établissement dans la carte Labyrinth.
