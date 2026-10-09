# Transport des rôles : conception proposée

Le rôle intérieur conserve une position structurelle et le lien entier déterminé par cette position. Le transport des positions suit le transport de l'épine et la réindexation explicite de `transport_deploy`. Il ne reconnaît pas une position par les seules valeurs des nœuds.

L'équivalence du rôle avec sa position suffit à assembler les retours exacts. Un lemme de lecture du lien réindexé, puis `mapSpine_link`, assure que la donnée successive entière est l'image du lien original : source, cible, compatibilité et provenances internes comprises.

Le rôle final suit `circularBoundaryTransport` et `EquippedFinalRole.exactTransport`, avec conservation des cinq données choisies. La somme inductive `CircularRole` conserve sa branche : intérieure ou finale. Aucune hypothèse d'obstruction, aucun transport de pôles arbitraires, aucune unicité de successeur n'intervient.

Les formations comparées sont la formation originale et celle reconstruite le long de la signature avec mêmes états et mêmes pas. L'assertion ne concerne pas deux générateurs indépendants.
