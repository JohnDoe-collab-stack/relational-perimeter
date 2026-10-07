# Plan de présentation et de vérification du calcul constitutif et de la machine

## Objet du travail

Présenter et faire vérifier le calcul dans son ensemble : les dépendances
constituées permettent une recherche ; les relations effectivement trouvées
autorisent une décomposition ; cette production devient une organisation qui
agit sur les entrées suivantes ; la continuation conserve les distinctions
nécessaires à ses futurs et peut abandonner les autres sous un contrat explicite.

L'objectif du dossier machine est de faire porter la continuation par cette
organisation produite, plutôt que de retrouver continuellement son action dans
une représentation historique séparée. Il faut montrer comment le logiciel
actuel réalise ce passage, et où une médiation représentative demeure. La
largeur des obligations en est une conséquence importante, pas le sujet unique.

Ce plan ne remplace ni les quatre paragraphes de la
[cible canonique](../conclusion-largeur-exponentielle-conservation-identites.fr.md),
ni S1–S8 et G1–G10 du
[protocole existant](ARISTOTLE_INTEGRATED_MASTER_MACHINE_AUDIT.md).
Il organise leur explication et l'examen de leurs raccords. Il ne promet pas
un verdict d'audit et ne transforme pas une présentation en démonstration.

## Point de départ et périmètre

Branche observée : `codex/integrated-master-machine-audit-20261006`.
Commit de départ : `39a3a352082e63c0fca27171d903bb367467b22c`.
L'arbre contient aussi des modifications et des fichiers nouveaux non commités,
notamment les politiques de regroupement partiel. Ce SHA seul ne désigne donc
pas l'ensemble étudié. Avant chaque lot, relever le diff et les empreintes des
fichiers concernés ; attribuer les résultats à cet état précis.

Le plan a d'abord été créé sans exécuter ses lots. L'autorisation de poursuivre
a ensuite permis la rédaction et les vérifications locales décrites en fin
de fichier. La suite doit respecter les autorisations demandées, le travail
des autres agents, les
[instructions du dépôt](../../AGENTS.md) et la
[procédure scientifique](../methode-de-travail-scientifique.fr.md).
Les fondations, la cible protégée, les contrats, les figures et l'instance
maître ne sont pas à changer pour améliorer la présentation.

Le [texte de travail actuel](TEXTE_CHAINE_CONSTITUTIVE_A_AUDITER.fr.md) sera
repris comme explication de la chaîne. Le
[plan de corrections antérieur](PLAN_CORRECTIONS_AUDIT_MACHINE_INTEGREE.fr.md)
reste distinct : ne pas effacer ses résultats ni présenter ce nouveau travail
comme une réouverture automatique de toutes ses corrections.

## Ordre de travail

```text
Relations primitives et témoins positifs
  -> histoires, occurrences et contextes constitués
  -> recherche effectivement exécutée
  -> relation trouvée et action, avec préservation séparée
  -> autorisation et décomposition produite
  -> programme configuré et continuation effective
  -> état suivant et mémoire sous contrat
  -> observations et lectures quantitatives
```

Pour chaque passage, renseigner quatre choses : ce qui constitue son type,
ce qui produit et lit effectivement ses données, ce que la preuve consomme,
et quelles distinctions sont conservées, regroupées ou oubliées. Un import,
un champ stocké ou une largeur constatée ne suffit pas à établir le passage.

### Lot un Reconstituer la chaîne de dépendances

Lire les définitions, leurs énoncés complets et leurs consommateurs dans
l'ordre ci-dessus. L'inventaire suivant donne les points de départ ; il ne
dispense pas de lire leurs dépendances transitives.

| Passage à établir | Sources à examiner | Ce que la fiche doit rendre vérifiable |
| --- | --- | --- |
| Fondation vers histoire et occurrences | Les quatre fichiers initiaux, [ConstitutiveGeneration](../../RelationalPerimeter/Computation/ConstitutiveGeneration.lean), [MasterResourceExecution](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/MasterResourceExecution.lean) | Les objets reçus par le calcul proviennent de cette constitution ; le carrier n'est pas un produit booléen ajouté indépendamment. |
| Histoire reçue vers recherche et étape produite | [CausalOperationalExecution](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/CausalOperationalExecution.lean), [ConstitutiveDiscovery](../../RelationalPerimeter/Computation/Machine/ConstitutiveDiscovery.lean), [ConstitutiveLiveExecution](../../RelationalPerimeter/Computation/Machine/ConstitutiveLiveExecution.lean) | Les données reçues sont réellement lues ; la tête est produite sans future queue ; la recherche retourne l'action effectivement utilisée. |
| Recherche SAT vers décomposition | [AcceptedFrontierNormalization](../../RelationalPerimeter/Computation/ConstitutiveSearch/AcceptedFrontierNormalization.lean), [MasterRuntime](../../RelationalPerimeter/Computation/Machine/MasterRuntime.lean) | `produceProblem` construit son code depuis les résultats du chercheur ; la relation trouvée et sa préservation autorisent le regroupement. |
| Code produit vers action sur une nouvelle entrée | [FrontierCircuit](../../RelationalPerimeter/Computation/Machine/FrontierCircuit.lean), [MasterRuntime](../../RelationalPerimeter/Computation/Machine/MasterRuntime.lean) | `lowerFrontier_exact` porte sur toute continuation typée ; `route_exact` raccorde l'effet au circuit installé ; `circuit_preserves_SAT` est une garantie séparée. |
| Production vers recherche suivante | [MasterRuntime](../../RelationalPerimeter/Computation/Machine/MasterRuntime.lean) | `advance_frontier_is_produced` expose la frontière reçue à la reprise suivante ; `advance_core_exact` expose le successeur vivant provenant de la production partagée. |
| Continuation vers mémoire exacte et distinctions nécessaires | [ReducedLiveContract](../../RelationalPerimeter/Computation/Machine/ReducedLiveContract.lean), [ReducedLiveMinimality](../../RelationalPerimeter/Computation/Machine/ReducedLiveMinimality.lean), [ConstitutiveLiveExecution](../../RelationalPerimeter/Computation/Machine/ConstitutiveLiveExecution.lean), [MasterContract](../../RelationalPerimeter/Computation/Machine/MasterContract.lean) | Exactitude des futurs, domaine de cohérence de la minimalité, et nécessité comportementale pour toute réalisation exacte du même contrat. |
| Organisation produite vers obligations et largeur | [ExecutedOutputObligations](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ExecutedOutputObligations.lean), [PublicRolePolicySpectrum](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/PublicRolePolicySpectrum.lean) | Le régime lit les cibles produites ; l'égalité de ses obligations correspond à leur codétermination ; les lectures de largeur arrivent après cette construction. |

Chaque fiche doit désigner le producteur, la sortie exacte et le consommateur.
Préciser aussi les entrées fournies à la construction et celles produites par
l'exécution. Une dépendance causale n'implique pas une nouveauté informationnelle.

Suivre les transports effectivement définis. Une préservation dirigée de SAT
n'autorise ni l'égalité des sources ni une loi de retour sur chaque source.
Lorsque deux lois de retour existent entre représentations, citer leurs
domaines exacts ; ne pas les attribuer à la transformation de regroupement.

**Sortie du lot :** une matrice de la chaîne entière avec références, types,
producteurs, consommateurs et statut de chaque raccord. Si une obligation
requise manque, l'inscrire comme manque ; ne pas l'effacer en changeant de cible.

### Lot deux Distinguer les contrats de continuation

Avant toute affirmation sur la mémoire, fixer les demandes permises, les
observations, les événements, les admissions et le domaine des états.

| Contrat | Ce qu'il couvre | Ce qu'il ne faut pas lui faire conclure |
| --- | --- | --- |
| Continuation des profils produits | Reprises et lectures de rôles admises par [ProducedProfileContinuation](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ProducedProfileContinuation.lean) | Ce contrat n'est pas celui des impulsions et routages de la machine intégrée. |
| Noyau machine V2 et sa réalisation réduite | Listes finies arbitraires de `advance`, `sample`, `pulse`, avec entrelacements et refus | Son théorème de minimalité ne porte pas automatiquement sur la mémoire SAT ajoutée. |
| Machine intégrée | Demandes du noyau, routages configurés et lectures du problème dans [MasterContract](../../RelationalPerimeter/Computation/Machine/MasterContract.lean) | L'admission d'un paquet brut ne démontre pas qu'il encode une continuation satisfaisant SAT. |
| Lectures restreintes après action | Lectures répétées de la variable 10 dans [VariableMasterFutures](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/VariableMasterFutures.lean) | Pas de reprise de recherche, d'impulsion ou d'inspection de toute l'histoire. |
| Signatures de continuation des agents | Comportements sur les états atteignables et sous les exigences du [contrat concerné](../signatures-de-continuation.fr.md) | Ni tout état brut, ni minimum physique de mémoire. |

Au noyau, distinguer l'exactitude sur toutes les mémoires sources de la
minimalité sur les mémoires sources cohérentes. Lire notamment `minimality`
et `any_realization` dans `ConstitutiveLiveExecution` : ils n'imposent pas les
mêmes champs ou le même encodage à toute réalisation ; ils interdisent de
confondre les distinctions encore observables dans ce contrat.

La mémoire SAT intégrée conserve sa frontière, lue par la recherche suivante.
L'exactitude de ses futurs est construite ; sa minimalité complète ne découle
pas de celle du noyau. Si le texte veut revendiquer cette minimalité complète,
c'est une nouvelle obligation formelle à annoncer et à faire autoriser, non
une conclusion déjà disponible.

**Sortie du lot :** une carte des contrats et de leurs compositions prouvées.
Aucune phrase sur l'oubli ou la nécessité ne reste sans contrat et domaine.

### Lot trois Montrer une exécution compréhensible du maître existant

Prendre le témoin de
[MasterIntegration](../../Tests/Machine/MasterIntegration.lean), sans créer un
autre moteur ni fournir une partition attendue : même maître public, formule
`[[positive 12, positive 1, positive 2]]`, profondeur, variable sélectionnée 12,
scope et chercheur. Seule la décision reçue auparavant sur la variable 1 change.

Exposer successivement :

1. Les deux histoires reçues et ce qui les distingue ; ne pas prétendre qu'elles
   sont deux sorties de la même course publique si seule leur réception est établie.
2. Les deux enfants de chaque ouverture, leurs distinctions et leurs
   continuations SAT positivement construites.
3. Les résultats du même chercheur : regroupement dans un cas, maintien des
   deux alternatives dans l'autre. L'échec signifie l'échec de ce chercheur,
   pas l'impossibilité de toute transformation.
4. Le code effectivement produit, sa conversion en circuit et son installation.
5. Une entrée ultérieure : le paquet `(0, [false])` est routé vers
   `(0, [true])` dans le cas regroupé et `(1, [false])` dans l'autre.
   Le slot peut être permuté ; ce n'est pas une conservation de ses numéros.
6. La reprise suivante, qui prend cette frontière retenue comme entrée et non
   un nouveau problème reconstruit seulement depuis la profondeur.

Les premières étapes et les effets des paquets possèdent déjà des preuves dans
le test. Raccorder explicitement la dernière à `advance_frontier_is_produced`
et au terme de `advance`. Si un exemple concret à deux reprises est nécessaire
à l'explication, calculer ses valeurs avant de les raconter ; ne pas inventer
son issue.

Présenter ensuite les témoins de mémoire avec leurs domaines propres, notamment
[ValidAssignmentForgetting](../../Tests/Machine/ValidAssignmentForgetting.lean).
Ne pas juxtaposer ce témoin et le scénario SAT comme s'ils formaient déjà une
seule trajectoire atteignable démontrant toutes les propriétés. Expliquer le
raccord général, puis identifier honnêtement les exemples qui l'illustrent.

**Sortie du lot :** un récit exécutable, avec une petite table des entrées,
productions et effets ; les témoins de mémoire restent explicitement situés.

### Lot quatre Mettre la machine au centre du texte scientifique

Réorganiser le texte de travail selon cet ordre :

1. Ce que construit le cadre : des dépendances, des histoires et des objets
   structurés sur lesquels le calcul agit.
2. Ce que produit l'exécution : la relation recherchée, l'autorisation et la
   décomposition, avant la continuation qui les reçoit.
3. Ce que devient cette production : un programme configuré qui agit ensuite
   sur des entrées variables sans recommencer la recherche.
4. Ce qui persiste : la frontière et l'état vivant effectivement produits,
   transmis à la reprise ; les mêmes productions fournissent effets et successeurs.
5. Ce que la mémoire peut oublier et doit distinguer : exactitude des futurs,
   minimalité comportementale du noyau et limites de sa composition avec SAT.
6. Les conséquences de largeur, leur portée exacte et leur lecture extensive aval.

La machine ne doit plus apparaître seulement en annexe après un développement
centré sur `2^n`. Les noms Lean vont dans la table d'évidence ; la prose doit
être compréhensible sans connaître ces noms ou les anciennes conversations.

Conserver le contraste essentiel : le regroupement ne détruit pas les identités
des profils sources ; un oubli de mémoire peut rendre certaines différences
irrécupérables, mais seulement lorsque les futurs du contrat ne les distinguent
plus. Ce sont deux opérations distinctes.

Dire précisément quelle représentation a disparu du chemin actif et laquelle
reste. Le circuit actuel est un programme logiciel interprété ; il n'est pas
encore une architecture matérielle. La frontière SAT agit sur la recherche SAT
suivante ; elle ne rétroagit pas actuellement sur le moteur vivant. L'absence
de recherche répétée sur le chemin configuré n'est pas l'absence de tout coût.

Pour les largeurs, séparer la lecture des profils, les obligations du régime,
la frontière SAT retenue et la banque mémoire. Le `iff` caractérise la pleine
largeur `2^n` des régimes surjectifs concernés. Les politiques partielles ont
largeur `2^k` dans la classe de statuts prouvée, pas dans tout régime imaginable.
Une politique non injective peut encore avoir largeur `2^(n-1)` : ne pas
transformer la caractérisation de la pleine largeur en élimination générale
de toute croissance exponentielle. Ces politiques comparatives ne sont pas
de nouvelles décompositions découvertes par la recherche SAT.

**Sortie du lot :** un texte complet dont le lecteur peut reconstruire ce qui
est produit, réutilisé et oublié, puis ses conséquences. La cible canonique
reste inchangée et référencée, sans copie concurrente faisant autorité.

### Lot cinq Raccorder chaque affirmation à son évidence

Pour chaque clause du texte, donner dans une table : objet et quantification,
contrat et hypothèses, producteurs et consommateurs, énoncés formels, témoins
construits, et statut de revue. Examiner les passages, pas seulement la présence
de tous les noms dans l'API publique.

Réutiliser les contrôles existants de partage des transitions et de provenance
des effets compilés. Leur rôle est de contrôler que le programme implémente
les dépendances annoncées ; ils ne remplacent pas les preuves sémantiques.
Leurs frontières locales ne certifient ni tout le tas, ni le coût physique total.

Si un raccord requis n'est établi que dans un test ou une ancienne sonde d'audit,
identifier l'énoncé manquant dans la production. Proposer alors la preuve locale
minimale sur le maître et les constructions actuels, sans réécrire une instance
plus facile. Les changements Lean restent un lot explicite, soumis aux audits
constructifs, à la stratification et aux régressions existantes.

Le [registre scientifique](../scientific-claims.json) possède déjà des entrées
pour le couplage, l'action configurée, les futurs et le partage. Déterminer si
la minimalité du noyau et l'explication de la chaîne entière nécessitent des
entrées supplémentaires ou des ancrages mieux répartis. Toute modification
rouvre la revue concernée. Ne pas actualiser des empreintes périmées simplement
pour obtenir un contrôle vert, ni reporter un verdict historique sur le nouvel arbre.

**Sortie du lot :** toutes les clauses majeures ont une évidence et une portée
vérifiées ; les obligations ouvertes restent visibles, sans verdict fabriqué.

### Lot six Relire et vérifier le paquet complet

Faire d'abord une lecture autonome de la prose : peut-on dire ce que reçoit la
machine, ce qu'elle trouve, ce qu'elle réutilise et ce qu'elle oublie sans ouvrir
une source Lean ? Confronter ensuite cette compréhension aux preuves complètes.
Contrôler aussi les passages français et anglais correspondants.

Pour le lot documentaire, vérifier les liens, les ancrages et le diff. Pour
le paquet destiné à l'audit, exécuter les gates complètes depuis une révision
figée avec la toolchain épinglée : `lake build`, `scripts/verify.sh`,
`scripts/verify.ps1` et les contrôles scientifiques inclus. Rapporter les
commandes, leurs résultats, l'état des revues et la révision effective.
Les nouveaux fichiers doivent disposer d'un commit de référence autorisé avant
de recevoir une évidence figée au registre.

Ne pas lancer un nettoyage destructif ou un build concurrent dans le checkout
d'un autre agent. La reproduction propre s'effectue dans un espace distinct.
Conserver les quatre fondations, les contrats, les résultats antérieurs et les
consommateurs agents. Les mesures ou tests nouveaux restent distincts des
preuves et des expériences confirmatoires déjà figées.

**Sortie du lot :** texte, sources et références cohérents sur le même paquet,
avec les limites explicites. Une gate réussie n'est pas encore un audit indépendant.

### Lot sept Préparer un audit de la chaîne et non de morceaux isolés

Après autorisation de publication, figer le SHA distant exact du paquet complet.
Préparer une nouvelle version du prompt ; ne pas retoucher un protocole déjà
soumis pour lui attribuer après coup une autre cible. Citer la cible canonique
inchangée, S1–S8 et G1–G10, puis le texte explicatif et sa table d'évidence.

L'auditeur doit examiner chaque passage de la chaîne et ses consommateurs,
la temporalité de la production, l'action sur les continuations, la préservation,
le partage des résultats, les futurs et leurs domaines. Il doit distinguer les
regroupements autorisés des singletons imposés, les états reçus des états
atteignables et la mémoire minimale du noyau d'une minimalité SAT non démontrée.
La largeur seule, les contrôles compilés seuls ou une collection de lots
indépendants ne suffisent pas à valider la chaîne revendiquée.

Demander une décision explicite sur chaque conclusion et chaque raccord
obligatoire, avec évidence. Aucun verdict global positif si un raccord requis
est faux ou demeure non établi. L'audit ne doit ni réparer le dépôt ni modifier
la cible. Sa soumission demande une autorisation distincte.

**Sortie du lot :** un prompt directement utilisable, épinglé à des fichiers
récupérables, et une liste exacte de conclusions à décider ; pas de verdict anticipé.

## Livrables et condition de clôture

Le chantier produira le texte explicatif revu, la carte des contrats, la table
des passages et une reproduction complète du paquet. Les documents scientifiques
canoniques seront mis à jour seulement après la revue correspondante ; aucune
nouvelle synthèse permanente n'est créée uniquement pour multiplier les documents.

Le travail est prêt pour l'audit lorsque la chaîne est lisible, chaque raccord
requis est construit et référencé, les domaines ne sont pas mélangés, et les
vérifications portent sur le même état que le prompt. Toute lacune nécessaire
bloque cette préparation ; aucune réduction de la cible ne la remplace.

Ce plan reste un document de chantier. Sa suppression avant une intégration
autorisée dans `main` suit les règles du dépôt. Aucun commit, push, changement
de branche, modification de figure ou envoi d'audit n'est autorisé par sa seule
existence.

## État du lot documentaire au 7 octobre 2026

Le [texte français](TEXTE_CHAINE_CONSTITUTIVE_A_AUDITER.fr.md) a été repris
dans l'ordre constitution, recherche, décomposition, action configurée,
continuation, mémoire et lectures de largeur. La
[version anglaise](TEXTE_CHAINE_CONSTITUTIVE_A_AUDITER.en.md) expose les mêmes
domaines et quantifications. La [table de preuves](PREUVES_CHAINE_CONSTITUTIVE_MACHINE.fr.md)
documente les passages C01–C10, les quatre lectures de dépendance, les données
fournies ou produites, et les cinq contrats distincts.

Le scénario du même maître est vérifié sur deux reprises : largeur un ou
deux selon l'histoire reçue, deuxième sélecteur 14, et effets des paquets
conformes aux circuits installés. Un client compile le raccord de la seconde
recherche et compose la préservation SAT existante. Aucune nouvelle instance
ni aucun producteur de remplacement n'ont été ajoutés.

Les gates locales passent ; leurs résultats et leur périmètre sont consignés
dans la table de preuves. Cette lecture porte sur les raccords cités, pas sur
une nouvelle lecture exhaustive de chaque ligne du dépôt. La reproduction
depuis une révision publiée figée et l'audit indépendant restent à faire.

Les sources, contrats, fondations, figures, cible canonique et registre figé
sont conservés. La minimalité du noyau est rendue explicite ; une minimalité
complète de la mémoire SAT intégrée n'est pas substituée à ce résultat.

La publication documentaire permanente, les nouveaux ancrages de registre et
le prompt épinglé du lot sept ne sont pas terminés : ils demandent une révision
de référence autorisée, la revue correspondante et, pour l'auditeur distant,
un SHA récupérable. Aucun commit, push ou envoi n'a été effectué pour ce lot.
