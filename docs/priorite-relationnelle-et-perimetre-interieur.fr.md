# Relations premières : ce que constitue le périmètre intérieur

La décision de départ du projet est claire : les relations sont premières. Les objets étudiés, leur identité et leur domaine doivent être constitués à partir de ces relations. Une collection d’objets déjà individués, puis munis de relations, ne sert pas de primitive à cette constitution.

Cette décision change les questions à poser aux preuves. Il faut expliquer comment apparaissent les places, ce qui individue une occurrence, comment un intérieur devient exactement déterminé et ce que l’on conserve en passant d’une construction à une autre. La présence de types et de fonctions dans Lean ne répond pas à ces questions à elle seule.

La première analyse Labyrinth vérifiait surtout les interfaces, les implications et leurs limites. Ces vérifications restent utiles, mais leur présentation ne faisait pas suffisamment apparaître ce déplacement. La présente reprise place la constitution de l’intérieur au centre. Elle concerne les fondations formalisées, sans étendre ses conclusions au chantier computationnel ni attribuer au projet une priorité historique non étudiée.

## Ce qui est reçu, ce qui est constitué

La formalisation reçoit des supports typés et des familles de relations. Dans `LocalNode`, les données explicites, implicites et de différence sont déjà accompagnées de témoins de compatibilité et de provenance. Dans `PositiveFormation`, des états, des nœuds équipés et des pas admissibles sont reçus avec leur lecture de compatibilité.

Ces supports permettent d’écrire les relations. Ils ne sont pas, à eux seuls, le domaine intérieur du périmètre. Celui-ci est constitué relativement à une présentation ou à une histoire précise : l’épine construit ses places non fermantes ; les histoires composables construisent leurs occurrences. Il n’est pas nécessaire de prétendre que la théorie engendre toutes les sortes primitives pour reconnaître cette priorité constitutive.

L’ordre des champs dans une déclaration Lean n’établit donc pas l’ordre de constitution du projet. La question pertinente est : quelle construction détermine le domaine et ses identités, et quelles opérations ne font qu’en lire une propriété ?

## L’intérieur est exactement déterminé

`PerimeterSpine` se construit par des avancées munies de témoins successifs. `NonClosingPosition` distingue les places de cette construction. `PositiveHistory` compose les pas d’une formation ; son déploiement donne une épine, et ses occurrences correspondent exactement aux positions de cette épine, avec deux lois de retour. La lecture du lien conserve les nœuds équipés et le témoin de compatibilité lu depuis le pas.

Dans le modèle historique, la reconstruction canonique établit aussi deux retours entre exigences intérieures et occurrences. Pour une réalisation exacte dans une histoire enracinée et composable, les preuves établissent l’injectivité, la conservation de la précédence et de la succession immédiate, puis la factorisation par la reconstruction canonique.

Cela donne un contenu précis au mot « intérieur » : chaque position a son occurrence constituée, chaque occurrence du déploiement canonique revient à sa position, et les relations organisent cette correspondance. Une histoire de réalisation plus longue peut contenir d’autres occurrences ; l’exactitude intérieure ne signifie pas que tout son domaine est l’intérieur du périmètre.

Un exemple rend la différence tangible. Deux pas peuvent lire le même nœud brut. Ils donnent pourtant deux occurrences distinctes, avec leur ordre et leur succession. Fusionner ces occurrences parce que leurs valeurs se ressemblent détruit la constitution de l’histoire. Le projet oblige à conserver ce qui les individue.

## La quantité précède sa lecture numérique

L’intérieur possède déjà une quantité structurale : quelles places sont constituées, quelles occurrences leur répondent, et selon quelles relations. Les correspondances exactes empêchent d’ajouter, de perdre ou de fusionner une occurrence intérieure dans les interfaces où leurs retours sont prouvés.

`History.length` fournit ensuite une lecture numérique, avec des lois sur les préfixes et les prolongements. Deux histoires de même longueur peuvent différer par leurs pas, leurs témoins, l’ordre de leurs données le long de la chaîne ou leur présentation. Conserver le nombre ne suffit donc pas à conserver la quantité constituée.

La question générale de quantité reste ouverte pour une signature commune et des critères de comparaison entre constructions arbitraires. Elle ne doit plus être présentée comme si aucune quantité intérieure n’était déjà formalisée. Les correspondances et leurs accords structurels constituent un résultat existant ; leur généralisation demande un travail supplémentaire.

## Un intérieur complet peut avoir une continuation

La complétude de cet intérieur tient à sa correspondance exacte avec les places constituées par l’épine relationnelle. Elle ne dit pas que toute génération doit s’arrêter. Le projet distingue ainsi l’accomplissement du tout constitué et la possibilité d’un pas ultérieur.

La jonction fermante, le rôle final et une occurrence ultérieure ont des fonctions différentes. Une jonction choisie peut munir la présentation de sa compatibilité fermante ; elle n’est pas une position intérieure supplémentaire. Le rôle final équipé garde les données de cette frontière. Une continuation strictement engendrée possède, elle, son occurrence propre dans l’histoire qui la produit.

La sortie du régime circulaire ne résulte pas de la seule existence d’une jonction. Dans les interfaces historiques examinées, elle mobilise les conditions de totalisation bilatérale et l’obstruction reçue qui rejette la tentative correspondante. La génération et le maintien dans un régime ont donc des critères distincts.

Les preuves permettent de penser ensemble un intérieur accompli, une continuation positive et un changement de statut. Cette articulation est l’un des intérêts centraux du projet ; la réduire à une classification de porteurs fait perdre ce qu’elle établit.

## Comparer exige de conserver la constitution

Un rôle final peut avoir un porteur contractile, lisible comme `Unit`, tout en restant indexé par une frontière et muni de données sélectionnées. Une équivalence de ce porteur ne décrit pas à elle seule le transport de la jonction, de la provenance, de la compatibilité et de leurs accords.

Les transports de signature, d’épine, de formation et de rôles traitent précisément cette exigence. Les transports de formation réalisés conservent les états et les pas entiers dans la formation reconstruite. Le simple déploiement d’une histoire peut, en revanche, oublier des données supplémentaires d’un pas au-delà de sa lecture de compatibilité : cette différence de portée doit rester visible.

De même, `CircularRole` déclare une grammaire intérieure/finale et prouve sa classification exacte. Ajouter une branche extérieure à une grammaire élargie montre seulement que cette classification n’est pas une exhaustivité universelle de tout type de rôles imaginable. Cela ne remet pas en cause l’exactitude de l’intérieur effectivement constitué. La justification ou la minimalité générale de cette grammaire reste une question séparée.

## Ce que la reprise de Labyrinth change

Les 93 fiches de la carte sont réexaminées sous quatre questions : données reçues, construction effectuée, lectures dérivées, portée de cette constitution. La validité des 58 résultats T2 et leur provenance restent séparées de cette nouvelle revue conceptuelle. Aucun résultat n’est promu en raison de cette reformulation.

La conclusion centrale devient : **le projet formalise la constitution relationnelle d’un intérieur, de ses identités et de sa quantité, puis étudie ses réalisations, ses transports et ses continuations.** Son intérêt tient aux distinctions que cette constitution rend obligatoires et aux résultats qui les respectent. Une comparaison avec d’autres programmes mathématiques doit partir de ces critères, puis examiner des travaux précis ; la simple liste des outils employés ne suffit pas.

Pour vérifier les énoncés et leur portée, lire la [carte détaillée](../labyrinth/FONDATIONS.fr.md), les sources [Primitives](../RelationalPerimeter/Constitution/Primitives.lean), [PositiveGeneration](../RelationalPerimeter/Constitution/PositiveGeneration.lean), [CircularRoles](../RelationalPerimeter/Constitution/CircularRoles.lean) et [StrongPerimetralTurning](../StrongPerimetralTurning.lean). La [convention des fiches](../labyrinth/STYLE.fr.md) distingue la revue des preuves de celle de leur lecture constitutive.
