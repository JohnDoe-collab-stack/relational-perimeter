# Livraison auteur — transport des rôles circulaires

## Résultat et périmètre

Le brouillon `CircularRoleTransport.lean.in` contient 26 déclarations auditées. Le noyau définit une équivalence exacte des positions entre le déploiement d'une histoire fournie et le déploiement de son histoire reconstruite le long d'un transport de signature. La réindexation utilise explicitement `transport_deploy.symm` après `map.positionTransport`.

Cette équivalence, encadrée par les deux transports exacts entre positions et rôles intérieurs, fournit le transport exact des rôles intérieurs et ses deux retours. La conservation du lien est une égalité du `SuccessiveLink` entier avec `map.mapLink role.link`. Elle conserve donc aussi les nœuds source et cible entiers, les témoins internes, la compatibilité successive et les provenances des deux nœuds. Les deux égalités de nœuds sont également exposées séparément.

Le rôle final suit `circularBoundaryTransport` et `EquippedFinalRole.exactTransport`. Les déclarations exposent la conservation de son témoin fermant, sa source, sa cible, la différence initiale et sa provenance. Le transport de `CircularRole` conserve chaque branche et possède les deux retours. Il commute avec la classification `NonClosingPosition ⊕ Unit` et la lecture `Option NonClosingPosition`.

Le transport concerne l'histoire originale et sa reconstruction, avec mêmes états et mêmes pas complets. Il ne fournit aucune comparaison arbitraire de deux formations préexistantes, ne transporte pas une obstruction ni des pôles arbitraires, et ne crée aucune position pour le rôle final. La classification est exhaustive relativement aux deux constructeurs de la grammaire déclarée.

## Modèles

`CircularRoleTransportExamples.lean.in` contient 28 déclarations auditées. Le modèle à trois pas du lot 3 est réutilisé avec le changement `witnessFlip`.

Les rôles à la première et à la troisième occurrence ont exactement le même lien entier mais restent distincts par leur position structurelle. Le transport conserve cette distinction. Il retourne les rôles des deux côtés, change les témoins Bool de compatibilité et de provenance comme prescrit, garde les branches intérieure/finale, commute avec les deux lectures et laisse le rôle final sans position générée.

## Contrôles effectués

- Compilation ciblée du brouillon de transport : succès, 26 audits sans axiomes (`transport-compilation.log`).
- Compilation ciblée des modèles : succès, 28 audits sans axiomes (`models-compilation.log`).
- Les premières erreurs de syntaxe/inférence sont archivées dans `first-compilation.log` et `first-models-elaboration-errors.log`. Elles concernent des calc incomplets et des paramètres implicites de signature, corrigés par égalités intermédiaires typées et arguments `F`/`T` explicites.
- Aucun contrôle global ni modification du journal, de la carte, du SOTA ou de fichiers canoniques par cet auteur.

La livraison est un travail d'auteur à faire relire indépendamment. Elle ne constitue pas une certification de referee.
