# Tranche 3B : changement exact de signature de formation

La construction envisagée reconstruit une formation à partir d'un transport de sa signature primitive complète. Elle conserve ses états et ses types de pas entiers. Elle transporte les nœuds, puis la lecture de compatibilité de chaque pas, par les applications reçues du lot 3A.

Cette voie ne suppose aucune inverse d'une application arbitraire entre pas. L'inverse des histoires reconstruites repose au contraire sur l'identité de leurs données `State` et `Step` et sur la récursion explicite. Une interface générale entre deux formations déjà données exigerait des accords supplémentaires, en particulier pour les pas et leurs lectures dépendantes ; elle n'est pas annoncée par cette construction.

Obligations visées :

- déploiement de l'histoire transportée égal au transport de l'épine initiale ;
- transport de la composition des histoires et retours exacts des histoires ;
- transport exact des occurrences, donc positivité conservée ;
- accord des positions avec celui du transport d'épines ;
- conservation et réflexion de la précédence et de la succession immédiate ;
- continuation choisie et marche finie reconstruites sans créer un nouveau choix de successeur.

Modèle visé : une lecture de compatibilité `Bool` échangée tandis que le pas entier reste inchangé. Des occurrences portées par des nœuds bruts identiques restent distinctes et gardent leur ordre. Les fonctions de pôles, l'obstruction historique et une classification générale des rôles ne font pas partie de cette tranche.
