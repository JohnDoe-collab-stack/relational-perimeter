# Plan de réparation du régime exécuté conforme au cadre constitutif

## 0. Statut du document

Ce document est un plan de chantier temporaire. Il doit être supprimé avant la
fusion dans `main`.

État de mise en œuvre : les trois verrous de causalité par étape, de dérivation
typée de `carry` et de fermeture de la chaîne scientifique publique sont
désormais implémentés. Les sections de diagnostic décrivent l’état antérieur à
la réparation ; les sections d’architecture décrivent l’implémentation exigée
et maintenant réalisée. La validation complète du dépôt reste une condition
d’achèvement.

Il conserve sans substitution la cible suivante :

> **Dans ce cadre, la constitution relationnelle des dépendances est primitive.
> Le calcul produit lui-même, pendant son exécution et à partir de ce qu'il a
> déjà produit, sa décomposition opérationnelle et détermine ainsi quelles
> alternatives doivent continuer à être traitées comme des obligations
> indépendantes.**
>
> **Cette exécution ne produit pas d'explosion exponentielle de la largeur
> opérationnelle : bien que le déploiement extensif des profils constitués ait
> une largeur 2^n, le régime exécuté les regroupe en une seule obligation sans
> identifier les profils eux-mêmes.**
>
> **Dans la classe binaire formalisée, une largeur opérationnelle exponentielle
> apparaît si et seulement si le régime impose de conserver séparément toute la
> multiplicité extensive, c'est-à-dire si son application `carry` est
> injective.**
>
> **L'explosion exponentielle de la largeur opérationnelle est donc démontrée
> ici comme l'effet exact de cette exigence extensive de conservation
> indépendante, et non comme une conséquence nécessaire de la structure
> relationnelle du problème elle-même.**

Le plan ne remplace pas cette cible par un résultat de cardinalité, un singleton
posé à l'avance, une comparaison de carriers voisins ou une reformulation
éditoriale plus faible. Si la chaîne causale décrite ci-dessous ne peut pas être
construite, la cible sera déclarée non atteinte.

## 1. Invariants imposés par la note sur le respect du cadre

La réparation doit respecter l'ordre suivant :

```text
relations primitives et témoins
  -> occurrences de rôle constituées
  -> histoire relationnelle dépendante
  -> profils d'occurrences déjà constituées
  -> carrier source de ces profils
  -> calcul et décisions opérationnelles
  -> régime d'obligations
  -> readout de la largeur du régime
```

En parallèle, la largeur source est obtenue seulement après constitution :

```text
profils d'occurrences déjà constituées
  -> frontière complète et sans doublon
  -> readout extensif de la longueur de cette frontière
```

Les règles suivantes sont non négociables.

1. La constitution appartient à la couche relationnelle, jamais à
   l'extensivité.
2. Une identité source est une occurrence, ou un profil dépendant
   d'occurrences, déjà constitué par l'histoire de rôles.
3. L'extensivité ne crée, n'individue et ne transforme aucune identité. Elle est
   uniquement le readout quantitatif d'une frontière déjà dérivée.
4. Le calcul ne recrée pas les identités sources. Il détermine leur statut
   opérationnel en construisant une réduction typée.
5. Un régime d'obligations est strictement en aval du carrier source. Son
   `carry` peut conserver ou regrouper des identités, mais ne les constitue pas.
6. L'égalité de deux obligations ne doit jamais devenir l'égalité des profils
   sources qui les portent.
7. Le readout extensif de la source et le readout de largeur du régime sont deux
   mesures dérivées. Le `iff` les relie sans transformer l'une d'elles en
   principe de constitution.
   Dans le paragraphe cible, « exigence extensive » désigne donc exclusivement
   l'exigence imposée à un régime de conserver séparément toute la frontière
   source ; elle ne désigne ni une puissance constitutive ni une couche qui
   agirait sur les identités.
8. Un transport exact peut comparer deux présentations déjà constituées. Il ne
   doit pas servir à fabriquer rétroactivement leur constitution ni à masquer un
   changement de carrier dans le théorème principal.
9. Une lecture homogène, par exemple une liste d'affectations, peut être
   extraite après la réduction. Elle ne doit pas remplacer les occurrences dans
   le carrier constitutif.
10. Les quatre fichiers fondateurs restent l'amont du projet. Aucun module de
    réparation ne peut leur faire importer une couche de calcul, de régime ou de
    mesure.

Conséquence immédiate pour ce chantier : le carrier source unique reste
`roleProfileFiniteCarrier roles`, dont les identités sont
`RoleOccurrenceProfile roles`. Le plan antérieur qui repartait de
`StructuralObligation` et de `structuralFrontier` est abandonné : il plaçait un
carrier du programme à la place du carrier constitué par les rôles et violait
la stratification ci-dessus.

## 2. Diagnostic exact de l'état antérieur à la réparation

### 2.1. Ce qui est déjà correctement constitué

La chaîne suivante est légitime et doit être conservée :

```text
exécution publique
  -> RelationalConstitutiveRoleHistory
  -> RoleOpeningOccurrence
  -> RoleOccurrenceProfile
  -> roleProfileFrontier
  -> roleProfileFiniteCarrier
```

Les propriétés suivantes sont déjà disponibles :

- chaque rôle est lu sur une étape causale exacte ;
- la relation reconstruite, son action, sa préservation et l'état suivant sont
  portés par `RelationalConstitutiveRoleStage` ;
- les occurrences gauche et droite sont constituées et distinctes ;
- un profil est une sélection dépendante de ces occurrences ;
- `roleProfileFrontier` est complète et sans doublon ;
- `roleProfileFiniteCarrier_width` donne ensuite le readout `2 ^ count` ;
- le théorème
  `roleConstituted_exponentialWidth_iff_distinctSeparateConservation` porte sur
  ce même carrier et sur tout régime surjectif qui en dépend.

### 2.2. Le défaut causal précis

Dans `ExecutedRoleIndexedReduction.lean`, le régime actuel n'est pas produit
par la réduction :

- `ExecutedOperationalObligation reduction` possède un seul constructeur et ne
  lit pas `reduction` ;
- `executedOperationalFrontier reduction` est la liste littérale
  `[.retained]` ;
- `carryByExecutedReduction reduction` ignore le profil et la réduction ;
- `executedObligationRegimeOfReduction` assemble donc un singleton constant ;
- sa largeur un et sa non-injectivité subsistent sans action relationnelle,
  sans préservation et sans exécution.

L'index `reduction` est ainsi fantôme dans la partie qui soutient actuellement
la conclusion publique.

### 2.3. Deux chaînes sont actuellement juxtaposées

Le dépôt contient :

- une chaîne d'exécution qui découvre réellement une transformation, exécute
  des candidats qui échouent, emploie une préservation séparée, retient une
  frontière et transmet sortie, graine et provenance ;
- une chaîne de régime qui obtient largeur un par une fonction constante.

Le certificat public place leurs résultats côte à côte, mais ne dérive pas le
second de la première. La réparation doit construire un raccord typé, pas une
égalité documentaire.

### 2.4. Le mauvais correctif à ne pas reprendre

Il ne faut pas déplacer le résultat vers :

- `ThreadedConstitutiveRoleHistory` ;
- `StructuralObligation` ;
- `structuralFrontier` ;
- un nouveau carrier de profils défini depuis le programme ;
- le carrier générique de `BinaryRelationalRoleExtensiveFamily` obtenu par un
  transport seulement propositionnel.

Ces objets peuvent rester des vues ou des résultats comparatifs. Ils ne peuvent
pas devenir la source constitutive du théorème réparé.

## 3. Architecture cible unique

La chaîne finale doit être littéralement celle-ci :

```text
executeConstitutiveResolution input
  -> publicInstrumentedExecutionRealization input
  -> buildStagewiseExecutedDecompositionHistory causalRun
  -> rôles et licences construits au préfixe de chaque étape
  -> RoleOccurrenceProfile stagewise.roles
  -> compileRoleHistory stagewise.roles
  -> stagewise.reduction
  -> reduceExecutedRoleProfile reduction profile
  -> executedRoleObligationRegimeOfStagewise stagewise
  -> readout de largeur du régime
```

La branche du readout extensif part du même objet constitué :

```text
RoleOccurrenceProfile roles
  -> roleProfileFrontier roles
  -> roleProfileFiniteCarrier roles
  -> longueur 2 ^ count
```

Le `iff` quantifie sur les régimes dont la source est exactement :

```lean
roleProfileFiniteCarrier roles
```

Le régime exécuté doit avoir exactement cette même source. Aucun transport de
carrier ne doit intervenir dans le contraste principal.

## 4. Réduction locale réellement relationnelle

### 4.1. Conserver la licence existante

`ExecutedRoleReductionLicense role atom` est le bon noyau local. Il distingue :

- l'occurrence transformée ;
- l'occurrence retenue ;
- l'action de l'atome relationnel ;
- l'égalité entre la sortie transformée et la sortie exécutée ;
- la préservation du critère ;
- la viabilité de l'occurrence retenue ;
- la distinction persistante des deux occurrences.

Cette licence ne doit pas être réduite à une étiquette `left/right` ni à une
preuve de largeur.

### 4.2. Ajouter une décision locale indexée par l'occurrence source

Introduire une famille de types de la forme suivante, avec un nom définitif à
choisir pendant l'implémentation :

```lean
inductive ExecutedRoleOccurrenceDecision
    (license : ExecutedRoleReductionLicense role atom) :
    RoleOpeningOccurrence role ->
    RoleOpeningOccurrence role -> Type
```

Elle doit avoir deux cas constructifs.

Le cas transformé doit certifier que :

- la source est `license.transformedOccurrence` ;
- la cible est `license.retainedOccurrence` ;
- l'interpréteur exécute réellement `atom.action` sur le payload typé de la
  source ;
- la sortie obtenue est la sortie complétée de l'étape ;
- la preuve de préservation séparée autorise cette réduction ;
- l'action est démontrée non identique sur la source exécutée ;
- aucune égalité entre occurrence transformée et occurrence retenue n'est
  produite.

Le cas retenu doit certifier que :

- la source est `license.retainedOccurrence` ;
- la cible est cette même occurrence retenue ;
- sa viabilité est fournie positivement ;
- aucune impossibilité de l'autre occurrence n'est invoquée.

Le constructeur canonique doit analyser l'occurrence effectivement fournie. Il
ne doit pas choisir un cas avant d'avoir lu sa position constituée.

### 4.3. Test substantiel de consommation

Les théorèmes principaux sur le cas transformé doivent mentionner dans leur type
ou leur preuve normalisée :

- `interpretRoleStageAtom atom` ;
- `license.transformedOutputExact` ;
- `license.transformedAccepted` ;
- `license.actionChangesSource`.

Si l'interpréteur ignore l'atome, si l'action est remplacée par l'identité ou si
la préservation est retirée, la décision locale transformée ne doit plus pouvoir
être construite.

## 5. Normalisation globale des profils déjà constitués

### 5.1. Profil retenu dérivé de l'histoire de réduction

Définir récursivement :

```lean
def retainedRoleProfile
    (reduction : ExecutedRoleReductionHistory (compileRoleHistory roles)) :
    RoleOccurrenceProfile roles
```

Au cas `step`, sa tête doit être
`license.retainedOccurrence`, lue dans la licence réelle, et sa queue doit être
dérivée de la réduction de queue. Il est interdit d'écrire un profil tout-droit
indépendant des licences puis de prouver ensuite qu'il leur correspond.

### 5.2. Trace globale dépendamment typée

Introduire :

```lean
inductive ExecutedRoleProfileReduction
    (reduction : ExecutedRoleReductionHistory (compileRoleHistory roles)) :
    (source : RoleOccurrenceProfile roles) ->
    (target : RoleOccurrenceProfile roles) -> Type
```

Sa récursion doit suivre simultanément :

- l'histoire de rôles ;
- le programme compilé depuis ces rôles ;
- l'histoire de réduction indexée par ce programme ;
- le profil source déjà constitué.

Chaque étape de la trace contient la décision locale de la section 4 et la trace
de queue. La cible globale doit être dérivée de ces décisions, puis prouvée égale
à `retainedRoleProfile reduction`.

### 5.3. Réduction totale

Conserver le normaliseur interne, puis construire positivement l’opération
dépendante qui fournit ensemble l’obligation et sa dérivation :

```lean
def normalizeExecutedRoleProfile
    (reduction : ExecutedRoleReductionHistory (compileRoleHistory roles))
    (profile : RoleOccurrenceProfile roles) :
    Sigma fun target => ExecutedRoleProfileReduction reduction profile target
```

```lean
def reduceExecutedRoleProfile
    (reduction : ExecutedRoleReductionHistory (compileRoleHistory roles))
    (profile : RoleOccurrenceProfile roles) :
    Sigma fun obligation =>
      ExecutedCarryDerivation reduction profile obligation
```

Il doit être exécutable et récursif structurellement. Il ne peut pas être fourni
comme hypothèse d'un certificat public.

Prouver ensuite :

- la cible est `retainedRoleProfile reduction` ;
- l'interprétation du profil source par le programme compilé produit les sorties
  complétées de l'histoire ;
- cette exactitude passe par les décisions locales et non par un théorème de
  largeur ;
- la normalisation ne produit aucune égalité entre le profil source et le profil
  retenu lorsque leurs premières occurrences diffèrent.

Cette trace est la formalisation du fait que le calcul détermine le statut
opérationnel des alternatives. La longueur de la frontière n'en est qu'un
readout ultérieur.

## 6. Régime d'obligations induit par la normalisation

### 6.1. Type d'obligation

Définir un type d'obligation dont la donnée est un profil retenu par la réduction,
par exemple :

```lean
structure ExecutedRetainedObligation
    (reduction : ExecutedRoleReductionHistory (compileRoleHistory roles)) where
  profile : RoleOccurrenceProfile roles
  retainedExact : profile = retainedRoleProfile reduction
```

Ce type est en aval des occurrences constituées. Il ne les redéfinit pas et ne
les quotient pas. Son unique valeur opérationnelle est obtenue à partir des
occurrences retenues par les licences.

### 6.2. Frontière opérationnelle dérivée

Définir la frontière à partir de `retainedRoleProfile reduction`, puis prouver
constructivement :

- sa complétude ;
- son absence de doublon ;
- sa longueur un.

Une frontière singleton est ici acceptable parce que son élément a été dérivé
de toute l'histoire de réduction. Le défaut actuel n'est pas la cardinalité un ;
c'est l'absence de dérivation du membre et de `carry`.

### 6.3. `carry` comme projection définitionnelle d'une réduction dépendante

Définir :

```lean
def carryByExecutedRoleReduction
    (reduction : ExecutedRoleReductionHistory (compileRoleHistory roles))
    (profile : RoleOccurrenceProfile roles) :
    ExecutedRetainedObligation reduction
```

L’opération primitive doit :

1. appeler `normalizeExecutedRoleProfile reduction profile` ;
2. prendre la cible produite par cette trace ;
3. construire l’obligation correspondante ;
4. retourner ensemble cette obligation et le témoin source-indexé qui la
   produit.

`carryByExecutedReduction` doit être seulement la première projection de cette
paire. Il est interdit de stocker une fonction `carry` indépendante, même
accompagnée ensuite d’une preuve d’égalité.

Il est attendu que les valeurs finales soient extensionnellement égales, puisque
la frontière a largeur un. Ce qui doit rester impossible, c'est de construire le
certificat causal public sans produire la trace pour chaque profil.

### 6.4. Paquet causal obligatoire

Ne pas exposer seulement un `ObligationRegime`. Introduire un paquet à
constructeur privé, par exemple :

```lean
structure ExecutedRoleObligationRegime
    (roles : RelationalConstitutiveRoleHistory run) where
  private mk ::
  reduction :
    ExecutedRoleReductionHistory (compileRoleHistory roles)
  reduce :
    (profile : RoleOccurrenceProfile roles) ->
      Sigma fun obligation =>
        ExecutedCarryDerivation reduction profile obligation
  reduceExact :
    (profile : RoleOccurrenceProfile roles) ->
      reduce profile = reduceExecutedRoleProfile reduction profile
```

La projection `.regime` définit elle-même son `carry` par
`fun profile => (package.reduce profile).1`. Le contenu ne peut pas être
affaibli : réduction, dérivation source-indexée, `carry` et frontière doivent
appartenir au même objet dépendamment typé.

Le constructeur canonique ne prend que `roles` et construit lui-même le programme
et la réduction canoniques. La projection `.regime` est le régime employé dans le
`iff` et dans la conclusion publique.

## 7. Même carrier pour la caractérisation et l'exécution

Le théorème central reste :

```lean
roleConstituted_exponentialWidth_iff_distinctSeparateConservation
```

Il quantifie déjà sur :

```lean
ObligationRegime (roleProfileFiniteCarrier roles)
```

La réparation doit donc construire le régime exécuté sur ce type exact. Le
contraste porte sur :

- `identityObligationRegime (roleProfileFiniteCarrier roles)` ;
- `(executedRoleObligationRegime roles).regime`.

Ils ont les mêmes identités sources, la même frontière source et la même histoire
relationnelle. Ils diffèrent seulement dans la manière dont le régime porte ces
identités comme obligations.

Le premier a un `carry` injectif et une largeur `2 ^ count`. Le second possède
une trace exécutée pour chaque profil, une largeur un et un `carry` non injectif
pour toute histoire non vide. Les deux profils témoins de la non-injectivité
restent distincts dans `RoleOccurrenceProfile roles`.

Le théorème générique sur `BinaryRelationalRoleExtensiveFamily` est conservé
comme généralisation comparative. Il ne doit plus être utilisé pour dissimuler
le passage vers un autre carrier dans le certificat principal.

## 8. Fermeture de l'instance publique

### 8.1. Interface conditionnelle et réalisation publique

`CausalConstitutiveStageExecution` peut rester une interface abstraite
conditionnelle. Une valeur construite par un appelant ne doit cependant pas être
présentée comme la réalisation publique exécutée.

Le certificat final doit être construit sans argument libre depuis :

```text
executeConstitutiveResolution input
  -> publicInstrumentedExecutionRealization input
  -> causalRun
  -> buildStagewiseExecutedDecompositionHistory
  -> rôles et licences au préfixe de chaque étape
  -> stagewise.reduction
  -> reduceExecutedRoleProfile
  -> executedRoleObligationRegimeOfStagewise
```

Une relation fournie directement par un appelant peut satisfaire l'interface
conditionnelle, mais elle ne doit pas pouvoir produire le certificat public qui
affirme que la recherche a reconstruit la relation après ses échecs mesurés.

### 8.2. Certificat public final

Réviser `ConstitutiveExtensiveSeparationCertificate` afin qu'il contienne une
seule chaîne, et non deux résultats juxtaposés :

- la réalisation instrumentée exacte ;
- la décomposition par étapes, construite canoniquement depuis le run exact ;
- les rôles constitués et leur exactitude ;
- le programme compilé depuis ces rôles ;
- la réduction exécutée ;
- le paquet de régime induit par cette réduction ;
- la réduction dépendante totale de tous les profils ;
- le readout source `2 ^ (input + 1)` ;
- le readout exécuté égal à un ;
- le `iff` sur le carrier exact des rôles ;
- deux profils distincts regroupés sans identification ;
- la transmission de la sortie, de la graine et de la provenance vers l'étape
  suivante, déjà prouvée dans la chaîne publique.

Aucun champ ne doit accepter un régime, une fonction `carry`, une relation, une
frontière ou une réduction fournis extérieurement. Le constructeur du
certificat est privé et son champ d’exactitude impose la décomposition
canonique du run public.

## 9. Consommation des relations sans confondre les couches

Le lemme cardinal général restera volontairement indépendant des relations. Ce
n'est pas un défaut : il décrit le rapport fini entre surjectivité, injectivité
et largeur.

La primitivité relationnelle du résultat intégré doit être établie ailleurs, par
la construction du régime public :

```text
relation reconstruite dans le rôle
  -> RoleStageAtom.action
  -> décision locale transformée
  -> trace globale de réduction du profil
  -> carry du régime exécuté
  -> largeur du régime comme readout
```

Ainsi :

- une famille abstraite aux relations triviales peut encore instancier le lemme
  cardinal ;
- elle ne peut pas, pour cette seule raison, produire le certificat causal
  public ;
- l'instance publique consomme réellement la relation reconstruite et sa preuve
  de préservation avant tout readout de largeur.

Cette séparation évite deux erreurs opposées : prétendre que le pigeonhole est
relationnel par lui-même, ou retirer les relations de la chaîne qui produit le
régime exécuté.

## 10. Modules et stratification

### 10.1. Modules constitutifs conservés

- `RelationalConstitutiveRoles.lean` : rôles lus sur l'exécution ;
- `RoleIndexedProfiles.lean` : occurrences et profils constitués ;
- `RoleIndexedProgram.lean` : programme en aval des rôles ;
- `RolewiseObligationRegime.lean` : `roleProfileFiniteCarrier` et `iff` sur le
  carrier exact.

Ces modules ne doivent importer aucun document quantitatif terminal ni aucun
certificat public synthétique.

### 10.2. Noyau de réduction

Conserver dans `ExecutedRoleIndexedReduction.lean` :

- `ExecutedRoleReductionLicense` ;
- `executedRoleReductionLicense` ;
- `ExecutedRoleReductionHistory` ;
- `buildExecutedRoleReductionHistory` ;
- les largeurs locales correctement dérivées.

Ajouter dans ce module, ou dans un nouveau module de même strate `D` si cela
évite un cycle :

- la décision locale indexée ;
- `retainedRoleProfile` ;
- `ExecutedRoleProfileReduction` ;
- `normalizeExecutedRoleProfile`.

### 10.3. Régime causal

Créer de préférence :

```text
EndogenousDecomposition/ExecutedRoleObligationRegime.lean
```

Ce module, classé dans la strate `D`, importe le noyau de réduction et
`RolewiseObligationRegime`. Il définit :

- `ExecutedRetainedObligation` ;
- sa frontière dérivée ;
- `carryByExecutedRoleReduction` ;
- le paquet privé `ExecutedRoleObligationRegime` ;
- sa construction canonique ;
- les théorèmes de largeur, de surjectivité et de non-injectivité.

Le manifeste `scripts/stratification.tsv` et les deux contrôleurs d'import
doivent être mis à jour. Aucun assouplissement de gate n'est admis pour faire
passer un import inversé.

### 10.4. Synthèse publique

Réviser ensuite :

- `PublicRelationalExtensiveFamily.lean` ;
- `ConstitutiveExtensiveSeparation.lean` ;
- la façade `EndogenousOperationalDecomposition.lean` ;
- les tests de régression concernés.

`PublicRelationalExtensiveFamily.lean` peut conserver les transports comparatifs
vers la famille générale. La conclusion intégrée doit cependant rester sur
`roleProfileFiniteCarrier roles`.

### 10.5. Suppression de l'ancien faux raccord

Après migration de tous les consommateurs, supprimer :

- `ExecutedOperationalObligation` sous sa forme singleton fantôme ;
- `executedOperationalFrontier` sous sa forme indépendante des licences ;
- `carryByExecutedReduction` constant ;
- `executedObligationRegimeOfReduction` actuel ;
- les théorèmes dont la causalité repose seulement sur ces définitions.

Les noms publics encore utiles peuvent être conservés comme alias vers les
nouvelles constructions seulement si leur type exprime la nouvelle dépendance.
Il est interdit de laisser l'ancien régime comme implémentation concurrente.

## 11. Théorèmes exigés avant toute révision documentaire

### 11.1. Constitution source

Pour toute histoire de rôles :

- le type source est `RoleOccurrenceProfile roles` ;
- sa frontière complète est `roleProfileFrontier roles` ;
- sa largeur est un readout égal à `2 ^ count` ;
- aucun de ces objets n'est défini depuis la largeur.

### 11.2. Exactitude locale

Pour chaque rôle et chaque occurrence :

- une décision locale est construite ;
- le cas transformé exécute l'atome relationnel ;
- la sortie est celle de l'étape exécutée ;
- la préservation est consommée séparément ;
- le cas retenu reste viable ;
- les deux occurrences restent distinctes.

### 11.3. Exactitude globale

Pour chaque profil :

- `normalizeExecutedRoleProfile` produit une trace ;
- la trace suit exactement l'histoire de réduction ;
- sa cible est `retainedRoleProfile reduction` ;
- la sortie homogène éventuelle coïncide avec
  `interpretRoleOccurrenceProfile` ;
- aucune mesure de largeur n'intervient dans cette construction.

### 11.4. Régime induit

Pour chaque profil :

- `regime.carry profile` est obtenu de sa trace ;
- le membre porté appartient à la frontière dérivée de la réduction ;
- la surjectivité du régime est construite ;
- la frontière du régime a largeur un.

### 11.5. Distinction sans indépendance

Pour toute histoire non vide, exhiber deux profils :

- distincts comme profils d'occurrences constituées ;
- munis chacun de leur trace de réduction ;
- portés vers la même obligation ;
- jamais identifiés dans le carrier source.

En déduire la non-injectivité du `carry` exécuté.

### 11.6. `Iff` exact

Pour tout régime surjectif sur `roleProfileFiniteCarrier roles` :

```text
largeur du régime = 2 ^ count
si et seulement si
regime.carry est injectif
```

L'adressage séparé est construit en factorisant par le régime. Il n'est pas une
hypothèse indépendante ajoutée au côté droit.

### 11.7. Deux régimes sur la même constitution

Construire positivement sur le même `roleProfileFiniteCarrier roles` :

- le régime identitaire, injectif, de largeur `2 ^ count` ;
- le régime exécuté causal, non injectif, de largeur un.

Le contraste ne doit modifier ni les rôles, ni les occurrences, ni les profils,
ni leur frontière source.

## 12. Matrice du paragraphe cible

### Phrase 1

Pour dire que la constitution relationnelle est primitive et que le calcul
produit sa décomposition, il faut simultanément :

- des rôles dérivés de la réalisation publique ;
- des occurrences constituées avant tout readout ;
- des atomes compilés depuis les relations de ces rôles ;
- une décision locale qui exécute l'atome sur le cas transformé ;
- une préservation séparée effectivement consommée ;
- une trace globale construite pour tout profil ;
- un certificat public impossible à construire depuis une relation fournie
  seule.

### Phrase 2

Pour dire que l'exécution regroupe les profils en une obligation sans les
identifier, il faut :

- le même `RoleOccurrenceProfile roles` comme source ;
- la largeur source `2 ^ count` obtenue comme readout ;
- un `carry` projeté de la trace exécutée ;
- une frontière opérationnelle dérivée du profil retenu par les licences ;
- une largeur exécutée égale à un ;
- deux profils distincts portés vers la même obligation.

### Phrase 3

Pour le `iff`, il faut :

- quantifier sur tout `ObligationRegime` sur le carrier exact des rôles ;
- utiliser sa surjectivité constitutive ;
- prouver séparément les deux directions ;
- dériver le readout source `2 ^ count` de la frontière des profils ;
- construire l'adressage à travers `carry` depuis son injectivité.

### Phrase 4

Pour conclure que l'exponentielle est l'effet exact de l'exigence extensive de
conservation indépendante dans cette classe, il faut :

- le `iff` précédent ;
- le régime identitaire exponentiel ;
- le régime exécuté causal de largeur un ;
- le même carrier source dans les deux cas ;
- la persistance des distinctions source ;
- une portée explicitement limitée à la largeur des régimes surjectifs
  formalisés, sans extrapolation à toute notion de complexité.

## 13. Vérifications de sensibilité obligatoires

Ces vérifications ne remplacent pas les preuves positives. Elles contrôlent que
les dépendances affirmées ne sont plus décoratives.

La construction du certificat public ou un théorème d'exactitude substantiel
doit échouer si l'on :

1. remplace la relation reconstruite par une relation fournie ;
2. remplace `RoleStageAtom.action` par l'identité dans le cas transformé ;
3. remplace l'interpréteur par une fonction qui ignore l'atome ;
4. retire `transformedOutputExact` ;
5. retire `transformedAccepted` ou la preuve de préservation ;
6. remplace le profil retenu dérivé des licences par un profil littéral écrit à
   l'avance ;
7. remplace `normalizeExecutedRoleProfile` par une cible constante sans trace ;
8. définit `carry` sans appeler le normaliseur ;
9. remplace le carrier source par un carrier de programme parallèle ;
10. applique le `iff` à un carrier seulement propositionnellement égal ;
11. reconstruit le certificat public depuis `CausalConstitutiveStageExecution`
    fourni par l'appelant ;
12. réintroduit l'ancien singleton fantôme.

Une fonction vers une obligation unique est nécessairement extensionnellement
constante. Ce fait ne constitue pas une mutation pertinente. La sensibilité
exigée porte sur la possibilité de construire la trace causale et le certificat
public, pas sur une variation impossible de la valeur finale dans un codomaine
singleton.

## 14. Ordre d'implémentation

### Phase A — verrouiller la stratification

1. Ajouter au plan de contrôle les invariants de la section 1.
2. Vérifier les imports actuels des modules de rôles, profils, programme,
   réduction et régime.
3. Ajouter le futur module au manifeste avec la strate correcte.
4. Écrire des contrôles qui interdisent aux couches de rôles et de profils
   d'importer les couches de régime, de largeur terminale ou de certificat.

Critère de sortie : le graphe d'import matérialise l'ordre constitutif avant tout
nouveau théorème.

### Phase B — construire la réduction locale

1. Définir `ExecutedRoleOccurrenceDecision`.
2. Construire les cas transformé et retenu depuis la licence existante.
3. Prouver l'usage exact de l'action et de la préservation.
4. Vérifier que la distinction des occurrences est conservée.

Critère de sortie : chaque occurrence constituée reçoit un statut opérationnel
par une preuve qui consomme réellement la relation exécutée.

### Phase C — construire la réduction globale

1. Définir `retainedRoleProfile` depuis les licences.
2. Définir `ExecutedRoleProfileReduction`.
3. Construire `normalizeExecutedRoleProfile` par récursion structurelle.
4. Prouver sa cible exacte et son accord avec l'interpréteur de rôles.

Critère de sortie : tout profil possède une trace calculable vers le profil
retenu, sans mesure de largeur et sans hypothèse externe.

### Phase D — dériver le régime

1. Définir `ExecutedRetainedObligation`.
2. Dériver sa frontière de `retainedRoleProfile`.
3. Définir `carry` par projection du normaliseur.
4. Construire la surjectivité.
5. Construire le paquet causal privé.
6. Prouver largeur un et non-injectivité sur histoire non vide.

Critère de sortie : supprimer la trace ou la réduction empêche la construction du
paquet employé par le résultat public.

### Phase E — reconstruire le certificat public

1. Remplacer l'ancien régime par le paquet causal.
2. Conserver `roleProfileFiniteCarrier roles` comme source unique.
3. Instancier le `iff` existant sur ce carrier exact.
4. Rassembler régime identitaire et régime exécuté dans une seule chaîne.
5. Fermer toute donnée à partir de l'exécution publique.

Critère de sortie : le paragraphe cible dispose d'une déclaration publique fermée
qui ne change jamais de carrier.

### Phase F — nettoyer sans régression

1. Migrer chaque consommateur de l'ancien régime.
2. Supprimer le singleton fantôme et ses théorèmes causaux illégitimes.
3. Conserver par dérivation honnête les résultats antérieurs encore vrais.
4. Mettre à jour les exports, le manifeste de stratification et les audits.
5. Ne modifier la documentation qu'après réussite de toutes les preuves.

Critère de sortie : aucun nom public, test ou document ne dépend de l'ancien faux
raccord.

## 15. Non-régression

La réparation doit préserver :

- les quatre fichiers fondateurs ;
- les occurrences constituées et leur histoire relationnelle ;
- les échecs réels de candidats pendant la recherche ;
- l'action sur des continuations arbitraires avant acceptation ;
- la préservation séparée ;
- la viabilité et la distinction des alternatives ;
- la dépendance de l'étape suivante à la sortie, à la graine et à la provenance ;
- la complétude et l'absence de doublon des profils ;
- le readout source exact `2 ^ count` ;
- le `iff` général sur les régimes surjectifs ;
- l'adressage factorisé par le régime ;
- les résultats de succinctness déjà établis ;
- la constructivité intégrale du dépôt.

La réparation ne doit pas introduire une seconde ontologie de profils ni une
seconde chaîne prétendument autoritative.

## 16. Discipline Lean

Pour chaque fichier créé ou modifié :

- aucune occurrence de `axiom`, `sorry`, `noncomputable`, `Classical`,
  `propext`, `Quot.sound`, `native_decide` ou `implemented_by` ;
- témoins construits positivement dans `Type` ;
- récursions structurelles exécutables ;
- aucune hypothèse externe ouverte dans l'instance publique ;
- exactement un bloc `AXIOM_AUDIT` final ;
- aucune preuve de l'égalité des profils tirée de l'égalité de leurs obligations ;
- aucune mesure numérique utilisée pour constituer les occurrences, les profils
  ou la réduction.

## 17. Validation finale

Depuis un arbre propre :

```text
lake clean
lake build +RelationalPerimeter
lake build
bash scripts/verify.sh
pwsh -File scripts/verify.ps1
git diff --check
```

Vérifier en plus :

- les deux scripts couvrent exactement les mêmes fichiers Lean ;
- tous les modules de production sont atteignables depuis `RelationalPerimeter` ;
- le contrôle de stratification réussit sans exception nouvelle ;
- `lake update` ne modifie pas le manifeste ;
- les quatre fichiers fondateurs sont inchangés ;
- aucun document temporaire ne sera fusionné ;
- les versions française et anglaise sont alignées ;
- chaque proposition du paragraphe cible renvoie à une déclaration publique
  précise ;
- les vérifications de sensibilité de la section 13 produisent les résultats
  attendus pour la bonne raison.

## 18. Critère d'achèvement sans substitution

La tâche est achevée seulement si un audit indépendant peut répondre oui aux
questions suivantes.

1. Les identités sources sont-elles exactement les profils d'occurrences déjà
   constituées par l'histoire relationnelle ?
2. L'extensivité est-elle seulement le readout de leur frontière complète ?
3. La relation reconstruite est-elle effectivement exécutée dans chaque cas
   transformé ?
4. La préservation séparée est-elle nécessaire à la construction de la décision
   locale ?
5. Chaque profil possède-t-il une trace de réduction calculable ?
6. Le profil retenu est-il dérivé des licences et non écrit à l'avance ?
7. Le `carry` du régime public est-il construit depuis cette trace ?
8. Le régime exécuté et le `iff` ont-ils littéralement le même carrier source ?
9. La largeur un est-elle le readout de la frontière dérivée de la réduction ?
10. Deux profils distincts sont-ils regroupés sans être identifiés ?
11. Le régime identitaire et le régime exécuté portent-ils la même constitution
    source ?
12. Le certificat public est-il fermé à partir de l'exécution réellement
    effectuée ?
13. Le `iff` reste-t-il général, bidirectionnel et non circulaire ?
14. Les résultats acquis sont-ils préservés sans seconde architecture
    concurrente ?
15. La décomposition de chaque étape est-elle constructible à partir de cette
    étape seule, avant toute queue future ?
16. Le `carry` est-il définitionnellement une projection de la réduction
    dépendante, sans fonction indépendante justifiée après coup ?
17. La chaîne employée par le certificat final est-elle inaccessible à toute
    relation qui ne provient pas du run public exact ?

Si une seule de ces conditions échoue, la cible n'est pas atteinte. Il est alors
interdit de remplacer la conclusion par un théorème plus faible ou de corriger
seulement le texte.
