# Constitution, calcul endogène et persistance : résultats et cible pour une architecture d’IA

Le projet construit un calcul dont les objets, les transformations et les
obligations sont suivis dans une même chaîne. Ce calcul ne reçoit pas seulement
des alternatives à examiner : il produit, pendant son exécution, les relations
qui déterminent comment poursuivre leur traitement. Ce qu’il a produit devient
ensuite une condition de la recherche suivante.

Cette chaîne permet de distinguer trois choses que la seule sortie ne montre
pas : l’identité d’un profil constitué, son statut d’obligation indépendante,
et sa présence dans la mémoire nécessaire à la continuation. Une distinction
peut rester établie dans l’histoire sans être conservée comme obligation
indépendante ; elle peut aussi devenir irrécupérable depuis la mémoire de
reprise, sans modifier les opérations futures expressément garanties.

L’objectif pour une architecture d’IA est de prolonger ce résultat : suivre les
déterminations pertinentes à travers les transformations du calcul, plutôt que
confondre leur persistance avec la conservation intégrale du passé ou avec
l’immobilité d’un état. Le présent document établit les bases de cette cible,
ses raccords au code existant et les obligations supplémentaires à démontrer.
Il ne présente pas cette transposition à l’IA comme déjà réalisée.

## 1. Statut du document et état de référence

Ce document est une note scientifique de référence, non un journal de chantier.
Il doit permettre de préparer une démonstration sans modifier ni affaiblir la
cible existante.

La relecture porte sur le dépôt `relational-perimeter`, branche
`codex/unified-foundation-master-instance`, à l’état
`75057f09cc9a535e8be3390999fa688c9ee3a96d`. Le dernier commit scientifique
soumis à l’audit de correction est
`8468f88448c51a0cd0ae178865fd014968131c47`.

L’audit indépendant antérieur a conclu à l’établissement de la cible
scientifique et demandé des corrections de l’unification. La nouvelle
soumission ne constitue pas un nouveau verdict : les corrections soumises ne
sont pas déclarées indépendamment validées dans ce document.

Les déclarations citées ci-dessous sont présentes dans l’état de référence ;
leurs définitions et preuves pertinentes ont été examinées. La rédaction
n’ajoute aucune preuve Lean, ne modifie aucun code et ne prétend pas remplacer
un build, un contrôle des chemins compilés ou un audit indépendant. Une
référence à une déclaration désigne ce qu’elle énonce effectivement, avec ses
indices et ses hypothèses.

Trois statuts seront distingués :

- **Résultat présent** : construction ou théorème identifié dans le dépôt.
- **Conséquence délimitée** : interprétation de ces résultats, dans leur portée
  formelle, sans déclaration supplémentaire annoncée comme prouvée.
- **Obligation de recherche** : ce qu’il faut encore construire et démontrer
  pour la transposition à une architecture d’IA.

## 2. La cible scientifique conservée

La cible suivante est conservée, et non remplacée par la cible future sur l’IA :

> Dans ce cadre, la constitution relationnelle des dépendances est primitive.
> Le calcul produit lui-même, pendant son exécution et à partir de ce qu’il a
> déjà produit, sa décomposition opérationnelle et détermine ainsi quelles
> alternatives doivent continuer à être traitées comme des obligations
> indépendantes.
>
> Cette exécution ne produit pas d’explosion exponentielle de la largeur
> opérationnelle : bien que le déploiement extensif des profils constitués ait
> une largeur 2ⁿ, le régime exécuté les regroupe en une seule obligation sans
> identifier les profils eux-mêmes.
>
> Dans la classe binaire formalisée, une largeur opérationnelle exponentielle
> apparaît si et seulement si le régime impose de conserver séparément toute
> la multiplicité extensive, c’est-à-dire si son application `carry` est
> injective.
>
> L’explosion exponentielle de la largeur opérationnelle est donc démontrée
> ici comme l’effet exact de cette exigence extensive de conservation
> indépendante, et non comme une conséquence nécessaire de la structure
> relationnelle du problème elle-même.

Cette citation reprend la [conclusion scientifique](conclusion-largeur-exponentielle-conservation-identites.fr.md).
Dans ce texte, « déploiement extensif » désigne la lecture quantitative des
profils déjà constitués, non une opération qui constituerait leurs identités.
La largeur exponentielle visée est la pleine largeur `2ⁿ`, non toute croissance
exponentielle imaginable d’un temps, d’une mémoire ou d’un autre régime.

Pour l’instance publique, `n = input + 1` est le nombre de rôles exécutés. Pour
le théorème de classe, `n` est le nombre de rôles de l’histoire considérée. Ces
paramètres ne doivent pas être confondus avec le nombre de variables d’une
instance SAT arbitraire.

## 3. La méthode et la stratification

La méthode est celle des rôles constitutifs relationnels : déclarer les
relations et les témoins reçus ; construire les objets qui les réalisent ;
établir leurs accords ; éprouver les dépendances ; reconstruire ce que le
support autorise ; transporter avec les lois nécessaires ; diagnostiquer les
changements de statut sur les mêmes objets.

Un rôle est déterminé par la formation, la source, la cible, la provenance et
l’inscription composable de son occurrence. Il n’est pas une étiquette libre
posée sur une valeur isolée. Le carrier est le support formel avec sa structure,
pas un ensemble dont les relations pourraient être oubliées sans examen.

Les dépendances constitutives se prolongent dans les producteurs exécutés :

```text
relations primitives et témoins reçus
    → états, pas et histoires libres constitués
    → matière produite pour la recherche
    → découverte et application de l’étape courante

étape exécutée → état suivant effectivement produit
étape exécutée + préfixe reçu → décomposition locale → préfixe suivant
état suivant + préfixe suivant → prochaine étape exécutée

étapes produites → histoire de rôles → profils dépendants
    → normalisation autorisée → obligations d’image
    → mémoire de continuation sous contrat
```

L’état suivant et le préfixe suivant ont donc des producteurs distincts. Le
premier vient de l’application exécutée ; le second incorpore la décomposition
locale au préfixe reçu. Ils sont raccordés dans le même successeur. Le schéma
ne prétend pas que la décomposition calcule l’affectation ou la graine de cet
état.

Cet ordre ne signifie pas que l’histoire complète des rôles computationnels
existe avant la recherche. Chaque rôle computationnel est indexé par l’étape
effectivement exécutée dont il expose les relations. L’histoire et les profils
complets sont dérivés de ces étapes avant leurs consommateurs scientifiques,
notamment le programme indexé par l’histoire et le régime global. La formation
de ces vues ne remplace pas la production locale qui a lieu dans la récursion.

Il faut ainsi distinguer l’ordre constitutif des dépendances, l’ordre des
producteurs exécutés et l’ordre dans lequel on expose ensuite leurs preuves.

Les lectures quantitatives sont en aval de leurs objets respectifs :

```text
histoire de rôles → carrier de profils → readout extensif
normalisation → régime d’obligations → readout de largeur opérationnelle
exécution instrumentée → compteurs du modèle de coût annoncé
```

Ces trois lectures ne se remplacent pas. En particulier, le nombre de profils
ne constitue ni le nombre d’obligations indépendantes ni le coût de leur
traitement.

Quatre questions doivent être posées à chaque raccord :

1. De quelles données et de quels indices dépend la formation de l’objet ?
2. Quel producteur construit effectivement cet objet à partir de ces données ?
3. Quels champs la démonstration considérée consomme-t-elle ?
4. Quelles distinctions sont conservées, oubliées ou reconstructibles après
   transport ou projection ?

Un champ présent dans un type n’est pas, pour cette seule raison, indispensable
à toute preuve du résultat terminal. Inversement, une preuve terminale courte
ne supprime pas les obligations nécessaires à la constitution et à
l’autorisation de l’objet auquel elle s’applique.

La [présentation française](relations-primitives-constitution-perimetre.fr.md)
fixe cette méthode et les distinctions entre construction, réalisation,
interprétation, admission et satisfaction d’une spécification. Elles restent
obligatoires dans l’extension computationnelle.

## 4. Ce qui précède le regroupement

### 4.1. Une constitution relationnelle, non un domaine ajouté après coup

Dans [StrongPerimetralTurning](../StrongPerimetralTurning.lean), `LocalNode`
porte des valeurs explicite et implicite, une différence, sa provenance et un
témoin de la famille `Compatible`. Les témoins successifs participent à la
constitution du périmètre ; les occurrences appartiennent à une histoire
enracinée et composable. Une occurrence et la valeur qu’une lecture lui attribue
ne sont pas interchangeables.

Les quatre fichiers initiaux restent la base du projet :

- [SegmentedResidualRole](../SegmentedResidualRole.lean) pour la détermination
  résiduelle sous segmentation fidèle ;
- [AbstractSegmentedTurning](../AbstractSegmentedTurning.lean) pour la
  continuation positive et la sortie d’un régime ;
- [ExactTypeTransport](../ExactTypeTransport.lean) pour les correspondances
  constructives avec deux lois de retour ;
- [StrongPerimetralTurning](../StrongPerimetralTurning.lean) pour la
  présentation et la génération périmétrales.

Leur présence ne signifie pas que chaque théorème résiduel ou chaque réfutation
de totalisation soit utilisé pour produire une instruction de recherche. Le
raccord computationnel consomme des données identifiables de la génération ;
il ne doit pas être décrit comme une déduction automatique de toute la
computation depuis chaque résultat fondamental.

La primitivité est interne à cet ordre de constitution. Lean fournit la
métathéorie d’implémentation ; le projet n’annonce ni son élimination ni une
fondation logique concurrente.

L’endogénéité est relative aux primitives reçues. Le calcul ne crée pas ses
propres types initiaux ou ses propres obligations normatives à partir de rien.
Ce sont les productions internes et leurs raccords, depuis ces données, qui
doivent être construits plutôt que fournis indépendamment.

### 4.2. Le générateur fournit réellement la matière suivante

[ConstitutiveGeneration](../RelationalPerimeter/Computation/ConstitutiveGeneration.lean)
part du périmètre canonique et itère le véritable `generate` depuis le point
terminal de l’histoire déjà produite. `successorOccurrenceSplit` construit une
correspondance réversible entre les anciennes occurrences augmentées d’une
place nouvelle et les occurrences de l’histoire prolongée.

À ce niveau, il n’existe encore ni critère d’acceptation, ni relation de
recherche, ni décision opérationnelle. La profondeur est une lecture de la
formation ; elle ne remplace pas l’histoire qui la rend disponible.

[ConstitutiveOperationalStage](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ConstitutiveOperationalStage.lean)
établit ensuite le raccord vers la racine de recherche. La génération suivante
est construite depuis la cible déjà produite. L’initialisation utilisée par le
calcul est celle de
[MeasuredGeneration](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/MeasuredGeneration.lean),
et non une seconde origine choisie parce qu’elle aurait la même profondeur.

### 4.3. La recherche effectue un travail, puis son résultat devient une action

[ConstitutiveFeedback](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ConstitutiveFeedback.lean)
contient `runThreadedNextDiscovery`. L’extraction utilise la génération et la
graine de l’état transmis ; le filtrage consomme sa provenance ; l’exploration
produit un résultat de découverte. Les échecs de candidats appartiennent à
cette exécution, et non à une histoire reconstruite pour expliquer une
transformation donnée d’avance.

`ThreadedConstitutiveStageRun` raccorde expressément la découverte retournée,
la construction de l’étape, le code issu de cette relation, son application et
l’état suivant. La famille publique est construite pour que les états frais
pertinents permettent cette découverte. Cela n’autorise pas à annoncer que
toute instance extérieure possède une telle transformation.

Les propriétés de la famille et certaines données initiales sont fournies par
sa construction. Le fait que la recherche retrouve effectivement une relation
dans cette famille n’est pas une preuve que sa valeur était imprévisible depuis
le paramètre. La provenance causale et la nouveauté informationnelle restent
deux questions distinctes.

### 4.4. L’action et sa préservation restent distinctes

Dans [RoleIndexedProgram](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/RoleIndexedProgram.lean),
l’atome de programme est fixé à la relation reconstruite par son rôle. Son
action transforme toute continuation de son domaine. La loi de préservation de
l’acceptation est prouvée séparément.

Cette séparation est une propriété des dépendances : définir l’action ne
demande pas une preuve d’acceptation de l’entrée. Elle n’affirme pas que la
preuve de préservation est recherchée plus tard dans le temps machine.

Pour l’occurrence transformée, l’interprétation applique cette action ; pour
l’occurrence retenue, elle conserve la continuation. Les accords de formation
placent chaque donnée dans le domaine approprié. Une action correcte sur la
seule entrée effectivement observée ne remplacerait pas cette action sur les
continuations arbitraires et sa loi de préservation.

Ce transport est dirigé. Il n’exige pas une application inverse et ne doit pas
être appelé bijection ou transport exact réversible sans ces données.

### 4.5. La sortie conditionne effectivement la prochaine recherche

`realizeNextOperationalState` construit l’affectation suivante, la génération,
la graine, la décision lue sur la sortie exécutée et la provenance. Les
théorèmes `nextDiscoveryConsumesProducedProvenance` et
`nextDiscoveryConsumesRetainedSearchSeed` établissent que la découverte
suivante lit ces matériaux dans l’état effectivement transmis.

Le lien n’est donc pas seulement « une étape vient après une autre ». Il est :
la première produit une donnée, et la seconde utilise cette donnée dans sa
propre constitution opérationnelle. Les valeurs canoniques de la graine
n’annulent pas ce raccord ; elles ne le transforment pas non plus en
information nouvelle.

### 4.6. La production locale précède la queue future

[MasterResourceExecution](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/MasterResourceExecution.lean)
enchaîne les producteurs `discover`, `applyStage`, `decompose` et `assemble`.
Leurs entrées sont des références typées aux ressources déjà disponibles.
`executeWithReferences` forme les ressources de tête, lit cette tête produite,
construit son successeur, puis poursuit la récursion depuis ce successeur.

[PrefixLocalOperationalProduction](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/PrefixLocalOperationalProduction.lean)
construit la décomposition depuis l’étape courante ; sa production ne reçoit
pas une histoire future achevée. Le préfixe reçu est un passé constitué,
indexé par l’état courant. Les lois de têtes exactes et d’indépendance de
l’horizon raccordent cette propriété à l’exécution maître.

`headNextSource` extrait le nouvel état de l’application exécutée ;
`headNextPrefix` extrait le préfixe de la production opérationnelle locale.
`continueWithReferences` les incorpore au support du même curseur suivant et
construit leurs transports de références. La recherche suivante lit l’état
transmis ; sa décomposition reçoit le préfixe transmis.

Le normaliseur global peut ensuite éliminer la chaîne conservée sur un profil
source. Cela ne doit pas être confondu avec une décision locale reconstruite
après observation du futur : les décisions locales qu’il consomme ont déjà été
produites à leurs étapes respectives.

L’ordre démontré porte sur ces producteurs et leurs dépendances, pas sur une
mesure de temps machine. L’égalité de deux résultats ne suffit pas à démontrer
qu’un exécuteur a été appelé une seule fois ; le partage de la construction et
les contrôles des chemins compilés sont des obligations distinctes.

## 5. Le changement de statut opérationnel

### 5.1. Les profils sont constitués avant leur lecture extensive

[RoleIndexedProfiles](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/RoleIndexedProfiles.lean)
construit les occurrences d’ouverture avec leur position, leur état engendré
et leur témoin de formation. Leurs profils sont des sélections dépendantes sur
l’histoire des rôles. Ils ne sont pas un produit de booléens auquel on ajoute
ensuite une provenance descriptive.

La frontière complète et sans doublon est dérivée de cette histoire. Pour
`n` rôles binaires, sa longueur vaut `2ⁿ`. L’extensivité est cette lecture
quantitative : elle ne constitue pas les profils et ne leur attribue pas, par
elle-même, un statut d’obligation indépendante.

### 5.2. Le regroupement doit être autorisé, pas seulement possible

[ExecutedCausalNormalization](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ExecutedCausalNormalization.lean)
conserve une chaîne constitutive exacte. Son résultat pour un profil est défini
par l’élimination de cette chaîne ; il n’est pas un champ de sortie libre.
L’action, son accord de sortie, la préservation et la séparation des
occurrences appartiennent à la chaîne et à l’autorisation qui en est extraite.

Il faut distinguer deux justifications :

- les sorties effectivement produites convergent, ce qui détermine l’image et
  permet d’en calculer la largeur ;
- les transformations préservent le critère et leurs occurrences sources
  restent distinctes, ce qui justifie le regroupement considéré.

Le théorème numérique de largeur ne doit pas être chargé, à lui seul, de toute
la causalité ou de toute la sémantique de l’autorisation. Une image singleton
arbitraire a aussi une largeur un ; ce n’est pas pour autant le régime autorisé
de cette exécution.

### 5.3. L’obligation est raccordée à la cible produite

Sur le carrier maître, les théorèmes `carry_fibres` et
`coDetermination_fibres` établissent :

```text
carry(p) = carry(q)
    ↔ target(p) = target(q)
    ↔ les traces exécutées de p et q codéterminent une cible commune
```

Ce raccord interdit d’ajouter, en aval, un regroupement sans rapport avec les
cibles produites. La réalisation exacte de l’image et l’autorisation
sémantique restent néanmoins deux interfaces distinctes.

`distinctPair` construit deux profils, prouve leur distinction et fournit leur
codétermination et leur portage dans la même obligation. La largeur un
n’établit aucune égalité de profils sources.

### 5.4. Ce que caractérise exactement le théorème exponentiel

Dans [FiniteExtensiveAddressing](../RelationalPerimeter/Computation/ConstitutiveSearch/FiniteExtensiveAddressing.lean),
un `ObligationRegime` possède une frontière finie complète, sans doublon, et
une application `carry` surjective depuis le carrier source. Pour un tel
régime fini, pleine largeur et injectivité de `carry` sont équivalentes.

La [classe de familles relationnelles](../RelationalPerimeter/Computation/ConstitutiveSearch/RelationalRoleExtensiveFamily.lean)
fournit, dans le cas binaire, la largeur source `2ⁿ`. Le résultat devient :

```text
largeur du régime = 2ⁿ ↔ carry est injective
```

L’adressage séparé est construit à partir de cette injectivité et passe par les
obligations du régime. Il n’est pas une seconde cause logique indépendante.
La surjectivité est essentielle à l’équivalence ; un codomaine contenant des
obligations étrangères n’est pas le régime ainsi défini.

`class_carrier_exact` et `class_iff_on_master_carrier` appliquent ce résultat
directement au carrier de l’instance maître, sans adaptateur. Sur ces mêmes
profils, le régime identitaire a largeur `2ⁿ`, et le régime exécuté a largeur
un. Les politiques partielles ont largeur `2ᵏ`, où `k` compte les rôles
conservés séparément ; elles ne sont pas annoncées comme autant de découvertes
effectivement exécutées.

Le lemme cardinal est général : il s’applique aussi à des relations triviales.
Il ne prouve donc pas, isolément, la nécessité d’un contenu relationnel non
trivial. L’apport de la chaîne est de construire les profils, leur action, leur
autorisation et leur régime exécuté sur les mêmes données, plutôt que
d’inférer un coût ou une indépendance depuis le seul nombre `2ⁿ`.

### 5.5. Le programme est opératoire, pas seulement une description plus courte

`compileRoleHistory_atomCount_exact`, dans
[RoleIndexedProgram](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/RoleIndexedProgram.lean),
donne un atome par rôle de l’histoire maître. Chaque atome est raccordé à son
action, pas seulement à une étiquette de position.

[ConstitutiveNormalizerSuccinctness](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ConstitutiveNormalizerSuccinctness.lean)
expose aussi le résultat public de programme succinct : `input + 1` atomes de
transport, une interprétation égale au normaliseur sur tout profil et toute
donnée acceptée de son interface `StructuralAcceptedPayload`, et les codes
effectivement retournés par la réalisation publique correspondante.

Les accords d’effacement de l’exécution maître raccordent celle-ci à la
réalisation publique existante. Ce sont des lois entre réalisations, non une
identification automatique de leurs types de programmes et de données. Le
compte d’atomes du programme maître et le théorème d’interprétation de cette
autre interface ont chacun le domaine indiqué par leur déclaration ; leur
raccord ne commande pas d’exécuter les deux réalisations à chaque reprise.

La différence avec une table de `2ⁿ` profils n’est donc pas seulement la taille
d’un texte qui la décrit. Le programme possède une action dont l’accord avec
la normalisation est démontré. La métrique de taille compte les atomes et les
codes locaux annoncés ; elle ne compte pas automatiquement les octets de
toutes les données capturées, les allocations ou le temps de découverte.

## 6. Persister n’est pas rester identique sous toute lecture

### 6.1. Trois niveaux d’identité

Il faut conserver trois questions différentes :

| Niveau | Question exacte | Résultat pertinent |
| --- | --- | --- |
| Occurrence historique | Quelle occurrence a été formée, à quel rôle et avec quelle provenance ? | Formation positive, indices historiques, séparation et transports des références. |
| Obligation opérationnelle | Deux profils doivent-ils être portés séparément pour l’opération autorisée ? | Égalité de `carry` exactement raccordée aux cibles produites. |
| Mémoire de reprise | La mémoire permet-elle encore de reconstruire le profil qui l’a produite ? | Irrécupérabilité du profil sous projection, avec exactitude du contrat futur. |

Une égalité au deuxième ou au troisième niveau ne se propage pas
automatiquement au premier. Une distinction au premier niveau n’impose pas
automatiquement son maintien aux deux autres.

Dans la perspective d’une persistance constitutive, une détermination doit
être suivie à travers les applications et les accords qui la concernent. La
répétition d’une même valeur observée, d’un même nom ou d’un même score n’est
pas ce suivi.

### 6.2. Les transports n’ont pas tous la même portée

Le dépôt fournit trois familles de passages, à maintenir séparées :

1. **Correspondances exactes de porteurs.** `ExactTypeTransport` donne deux
   fonctions et deux lois de retour. Il ne fournit pas automatiquement la
   conservation de toute relation portée par leurs domaines.
2. **Actions dirigées sur continuations.** L’action reconstruite fournit une
   transformation et une préservation d’acceptation. Elle n’est pas supposée
   réversible sur toutes ses entrées.
3. **Plongements historiques de références.** `Support.Extension` conserve le
   type, la lecture et la distinction des anciennes références dans le support
   réellement étendu. Ce plongement n’est pas une bijection vers toutes les
   ressources nouvelles.

Dans [ConstructedSupport](../RelationalPerimeter/Constitution/Resources/ConstructedSupport.lean),
le producteur lit ses arguments par des références antérieures et calcule le
type de sa sortie comme sa valeur. La formation enregistre cette production,
pas une sortie indépendante accompagnée d’une provenance ajoutée après coup.
Le prolongement maître compose les transports de références construits avec
les ressources nouvelles.

`Instance.grow` repart du curseur atteint et exécute seulement le suffixe
nouveau. `Growth.resume` poursuit ce résultat. Les raccords historiques,
leurs lectures et leur composition sont prouvés ; l’égalité avec une exécution
ininterrompue est une loi, pas une instruction de réexécuter le passé.

### 6.3. La cohérence porte aussi sur les données transportées

Atteindre le même profil normal ne suffit pas à garantir que deux chemins ont
transporté la même continuation.

[RoleGroupingSemantics](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/RoleGroupingSemantics.lean)
prouve `every_normalizing_trace` puis `normalization_coherent`. Pour une
politique de statuts fixée, deux traces normalisantes partant du même profil
vers son profil sélectionné transportent la même donnée arbitraire vers la
même donnée cible. La préservation d’acceptation de chaque trace est démontrée
séparément.

Cette cohérence ne signifie pas que toutes les politiques ou tous les profils
sources ont la même action. Elle délimite précisément quand l’action ne dépend
plus du choix entre les traces normalisantes autorisées.

### 6.4. Une sortie observée ne détermine pas l’action totale

[ExtensionalOperationalStability](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ExtensionalOperationalStability.lean)
construit un séparateur attaché à l’instruction faisant autorité. Son transport
et un transport de comparaison ont la même vue sous la projection définie et
la même sortie sur l’entrée exécutée, mais agissent différemment sur une autre
continuation du même domaine structurel. Appartenir à ce domaine signifie
réaliser les décisions structurelles de la source ; cela ne signifie pas, à
soi seul, satisfaire le critère d’acceptation.

La non-factorisation exclut la reconstruction de cette action totale depuis
cette seule projection, sur ce domaine. Elle n’exclut pas toute représentation
possible du calcul.

Pour la cible sur l’IA, la conséquence est précise : vérifier une réponse
observée ne suffit pas à vérifier ce que l’action ferait sur les autres
entrées de son domaine. Le suivi des accords relationnels et des lois
d’action apporte une garantie différente d’un accord ponctuel de sorties.

## 7. La continuation après la perte d’une distinction

### 7.1. Une même exécution, deux interfaces

[UnifiedPublicCertificate](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean)
forme `publicInstance` depuis un résultat de l’exécuteur par ressources. Les
rôles, le programme, la réduction, la normalisation, le régime, les références
et le curseur sont raccordés à ce résultat commun. `Facts` et `certificate`
réunissent les lois portant sur cette instance ; ils ne deviennent pas la
mémoire conservée par le moteur de reprise.

L’interface historique garde le profil source et son résultat de
normalisation. L’interface de reprise contient :

- l’état vivant, avec les matériaux encore lus par la découverte suivante ;
- la cible opérationnelle effectivement produite ;
- les lecteurs extraits des continuations de cette cible.

Le moteur vivant conserve notamment l’affectation, la génération, la graine et
la provenance. Il n’est donc pas présenté comme une mémoire vide, comme une
mémoire minimale ou comme la suppression de toute information historique.

### 7.2. Le contrat futur est défini avant la revendication d’oubli

[ProducedProfileContinuation](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ProducedProfileContinuation.lean)
autorise deux opérations :

1. avancer le moteur réel d’un nombre demandé de pas ;
2. lire une variable dans une continuation de la cible de normalisation déjà
   préparée, à l’un des rôles de cette histoire.

Une inspection est admise exactement lorsque l’adresse du rôle est dans la
borne des lecteurs produits. Sa réponse est raccordée à la continuation
effectivement produite, pas seulement à une seconde fonction choisie pour
renvoyer la même valeur. Une inspection hors borne n’est pas une opération
admise du contrat.

Dans ce contrat, `advance` fait évoluer l’état vivant, mais conserve la cible
préparée et ses lecteurs. Il n’ajoute pas de lecteur pour chaque nouveau rôle
produit par le moteur. La borne des inspections reste donc le nombre de rôles
de la normalisation préparée, non la profondeur ultérieure du moteur.

Le contrat ne contient pas une demande de reconstruction du profil source,
ni une consultation arbitraire de l’archive historique, ni toute interaction
possible d’un futur agent. Ces exclusions font partie de la portée annoncée,
et ne doivent pas être introduites après observation d’un échec.

### 7.3. L’exactitude se ferme sous toutes les suites finies de requêtes

[ContinuationContract](../RelationalPerimeter/Constitution/Grouping/ContinuationContract.lean)
distingue une source riche, une mémoire réduite, leurs transitions, leurs
admissions, leurs événements et leurs lectures. Son accord central est :

```text
projeter le successeur riche après une requête
    = exécuter cette requête depuis la mémoire projetée
```

Il faut aussi fournir l’accord des événements et des lectures, ainsi que les
deux transformations des témoins d’admission. La loi de transition ne les
remplace pas.

Dans l’instance, `next_exact` raccorde le moteur vivant au véritable successeur
du curseur par ressources. `sourceRun_is_resource_execution` relie sa
continuation riche à l’exécuteur déjà présent. `execute` puis `executeRequests`
partagent chaque production entre l’événement et son successeur.

Dans ce contrat concret, `sourceRead` et `sourceAllow` sont définis par les
lectures et l’admission de la mémoire projetée. Leur accord ponctuel est donc
définitionnel. Il ne prouve pas la conservation d’une observation historique
choisie indépendamment. Les raccords des transitions et des événements
d’avancement, eux, utilisent les lois du moteur réel ; l’inspection dispose en
outre d’un accord avec les lecteurs de la cible effectivement produite.

L’induction sur les requêtes donne `all_future_events` et `all_future_reads`.
L’admission est transportée et réfléchie. Les lectures garanties sont celles
du contrat, non toutes les propriétés de la source riche. Ce résultat est
donc plus qu’un accord sur l’état actuel, mais moins qu’une restitution
intégrale de l’histoire.

### 7.4. Ce qui est irréversiblement perdu

Deux profils distincts, construits sur les mêmes rôles publics, normalisent
vers la même cible et donnent la même mémoire pour un même curseur de reprise.
À ce curseur fixé, `memory_fibres` raccorde exactement cette égalité de
mémoires à celle des cibles produites.
`profile_not_recoverable` exclut un décodeur qui retrouverait correctement
chaque profil source depuis cette seule mémoire.

Il s’agit d’une impossibilité de reconstruction uniforme du profil, non de
l’impossibilité de choisir un représentant ni de deviner une entrée
particulière. Les profils restent distincts dans l’interface historique.

Comme les mémoires sont égales, toutes les suites finies de requêtes du contrat
produisent les mêmes événements futurs. La distinction perdue n’est donc pas
requise par ces opérations. Cette conclusion ne doit pas être étendue à une
opération nouvelle qui consulterait précisément la distinction oubliée.

Enfin, l’oubli des profils de normalisation n’est pas l’oubli des préfixes
chronologiques canoniques. Certaines données chronologiques demeurent
reconstructibles depuis la profondeur et la provenance conservées. Le
théorème d’irrécoverabilité ne doit pas être déplacé sur ces données.

## 8. Ce que toute la chaîne apporte à une architecture d’IA

### 8.1. Les objets de son action ont une constitution identifiable

La transposition ne consiste pas à ajouter une provenance à une réponse déjà
produite. Elle demanderait de construire les objets opératoires de l’agent à
partir de relations et de témoins localisés, puis d’indexer les actions par ces
objets. Une observation, une hypothèse ou un engagement ne pourrait être
remplacé par une donnée de même lecture sans vérifier les accords nécessaires.

Le dépôt fournit cette discipline sur ses occurrences et ses rôles. Il ne
fournit pas encore les objets d’un modèle de langage ou d’un agent général.

### 8.2. La suite dépend des productions antérieures

Le moteur actuel ne consulte pas seulement un récit du passé : il consomme les
sorties antérieures dans la construction de la prochaine recherche. Pour un
agent, cette propriété ferait de certains résultats acquis des conditions
opératoires de ses prochaines actions, avec une provenance et des raccords
contrôlables.

Ce n’est ni la succession seule, ni l’apprentissage seul. Une suite d’appels à
un modèle, un journal de messages ou une modification de poids ne garantit
pas, pour cette seule raison, le raccord démontré par le projet.

### 8.3. Les obligations peuvent changer sans effacer les objets

Le regroupement autorisé montre comment une différence constituée peut cesser
d’exiger un traitement indépendant pour un critère déterminé. Pour un agent,
il pourrait s’agir d’une différence entre deux voies de résolution devenues
opérationnellement codéterminées par une action effectivement reconstruite.

Le mécanisme n’est pas caractérisé par la seule coupe d’une branche. Il
comprend ce qui a été découvert, l’action disponible sur les continuations,
sa préservation, la viabilité et les liens vers la suite. Il n’exige ni de
déclarer la voie absorbée impossible ni d’identifier ses occurrences avec
celles de la voie retenue.

L’instance publique regroupe à chaque étape exécutée. Elle ne démontre pas
encore une découverte générale de partitions variées sur des entrées d’IA
arbitraires. Les politiques partielles servent à séparer les statuts sur le
même porteur ; leur existence ne constitue pas cette découverte supplémentaire.

### 8.4. Une mémoire réduite peut préserver des possibilités d’action

Le résultat de continuation montre comment abandonner une information source
tout en préservant un ensemble explicite de transitions, d’événements,
d’admissions et de lectures. Pour un agent, l’enjeu ne serait donc pas seulement
« résumer un contexte », mais prouver que les possibilités d’action promises
restent exactement disponibles après une réduction de mémoire.

Ce résultat est relatif à un contrat. Il ne sélectionne pas automatiquement
ce que l’agent devrait pouvoir faire demain et ne calcule pas une mémoire
minimale pour toute demande future.

### 8.5. La persistance recherchée est celle de déterminations suivies

La cible future peut être formulée ainsi :

> Construire une instance d’agent dans laquelle les déterminations pertinentes
> sont positivement constituées, utilisées par les actions successives et
> suivies à travers les transports requis ; démontrer que ces déterminations
> conservent leurs garanties sous les transformations autorisées et sous une
> réduction de mémoire dont le contrat futur est défini explicitement.

Cette persistance ne demanderait pas que chaque état, chaque représentation ou
chaque distinction historique demeure inchangé. Elle demanderait de préciser
ce qui persiste, par quelle application, à quels indices et avec quelle loi.

L’autorisation d’une action par le critère du dépôt ne constitue pas encore
l’alignement d’une IA sur une exigence humaine. Pour obtenir ce dernier
résultat, il faudra constituer cette exigence, son sens opérationnel et ses
témoins, puis démontrer leur raccord à une instance réelle. Il ne suffira pas
de renommer le prédicat d’acceptation « alignement ».

## 9. Ce qu’il reste à démontrer pour cette transposition

Il faut conserver le mécanisme existant et construire ses nouvelles
applications, non déclarer la cible atteinte en baptisant autrement les
interfaces actuelles.

### 9.1. Une exigence et une détermination concrètes

Choisir un objet pertinent pour l’agent et une exigence dont le contenu ne soit
pas défini uniquement comme « ce que cet agent produit ». Fournir positivement
ses relations de formation et de provenance, sa réalisation, puis les témoins
concrets requis par l’instance.

Le type de la détermination et les lois attendues doivent être fixés avant de
construire la réduction. Leur présence dans un index ne suffit pas à montrer
qu’elles gouvernent l’action.

### 9.2. Un domaine d’interaction non vide et pertinent

Définir les entrées réellement reçues, les opérations autorisées, les
observations promises et les réponses négatives. Construire des usages
concrets qui satisfont ce contrat, plutôt qu’un contrat réduit à des opérations
qui ne consultent rien de pertinent.

Le contrat actuel fournit une reprise réelle et des inspections non vides.
L’élargir à un agent exige de nouvelles lois, et non une extrapolation de
`advance` et `inspect` à toute interaction.

Si l’agent doit aussi consulter les nouvelles productions après chaque
avancement, il faudra construire leurs lecteurs et démontrer l’évolution du
contrat d’inspection. Le contrat actuel ne fournit pas cette extension.

### 9.3. Des actions produites et des garanties consommées

Les transformations doivent être produites depuis les données réellement
disponibles à l’étape courante. Relier leur action aux objets constitués,
démontrer leur préservation sur le domaine annoncé et construire les
successeurs à partir de leurs sorties.

Pour chaque garantie, séparer son rôle dans la formation, dans la production,
dans la preuve et dans l’autorisation. Un indice fantôme, une preuve seulement
stockée ou un accord ajouté après choix d’une cible ne ferme pas cette
obligation.

### 9.4. Un théorème de suivi à travers la chaîne entière

Énoncer les accords locaux sur une même détermination constituée, puis prouver
leur composition le long d’une histoire dépendante. Le théorème doit préciser
quelles relations sont conservées à chaque passage et quelles lectures
peuvent perdre des distinctions.

La quantification recherchée doit être fixée explicitement : pour chaque
entrée initiale admise de l’instance d’agent choisie, pour chaque histoire
produite par son moteur et pour chaque suite finie de requêtes admises par son
contrat, le suivi de la détermination doit se composer et les garanties
annoncées doivent rester établies. La formation de l’histoire et les témoins
initiaux doivent être construits ; ils ne doivent pas être remplacés par une
histoire quelconque supposée déjà posséder ces garanties.

Aux changements de type ou de représentation, ce suivi exige des applications
et des accords explicites. Une affirmation d’égalité entre des valeurs de deux
strates ne remplace pas le transport de la détermination et de ses témoins.

Le dépôt possède plusieurs de ces accords, leur composition et une façade
commune. Il n’existe pas encore, dans les résultats cités ici, un théorème
portant sur une détermination d’IA concrète depuis sa constitution jusqu’à
toutes ses interactions futures.

### 9.5. Une réduction de mémoire justifiée par le contrat de l’agent

Construire la mémoire réduite depuis les productions de la même exécution.
Démontrer les accords de transition, d’événement, de lecture et d’admission,
puis les fermer sur toutes les suites finies d’entrées du contrat.

Lorsqu’un oubli irréversible est annoncé, fournir deux sources distinctes
effectivement admises par l’instance, leur même mémoire réduite et
l’impossibilité d’une reconstruction uniforme. Vérifier que la distinction
oubliée n’est pas simultanément exigée par une lecture que le contrat promet.

### 9.6. Un raccord vers le calcul d’IA effectivement exécuté

Si un modèle, un planificateur ou un composant appris intervient, préciser ce
qu’il propose et ce qui est contrôlé avant admission de son action. Un
théorème sur un moteur abstrait ne certifie pas automatiquement ses propositions
ou son implémentation extérieure.

La preuve finale doit concerner l’instance construite, avec ses entrées, ses
actions et son mécanisme de continuation. Une interface générique dont les
hypothèses restent ouvertes est un contrat conditionnel, pas cette instance.

## 10. Critères de fidélité de la démonstration future

La mise en œuvre devra satisfaire ensemble les exigences suivantes :

- les lectures et les consommateurs utilisent les objets et rôles constitués,
  sans substituer une lecture à leur formation ;
- la constitution positive n’est pas remplacée par une existence
  propositionnelle non réalisée ;
- chaque action utilise des ressources antérieures identifiées, et sa sortie
  est celle de son producteur ;
- chaque tête est produite sans lire une queue future achevée ;
- les transports portent les lois relationnelles nécessaires, pas seulement
  des égalités de nombres ;
- l’autorisation de regroupement reste distincte de la réalisation de l’image ;
- l’égalité des obligations reste raccordée aux cibles produites, sans
  identifier les profils sources ;
- la mémoire de reprise et l’archive scientifique restent deux interfaces ;
- toute perte d’information annoncée est située sur une projection précise,
  avec un contrat futur fixé et une preuve de non-reconstruction appropriée ;
- les garanties d’une exigence d’IA ne sont pas remplacées par celles d’un
  critère plus faible ;
- toutes les hypothèses requises pour l’instance sont fermées par des témoins
  construits ;
- les données dans `Type` restent exécutables et les preuves constructives,
  conformément aux règles du dépôt.

Ces critères servent à écrire la démonstration. Des tests ou des mutations
peuvent révéler un raccord absent ; ils ne remplacent pas les constructions et
les lois qui le ferment.

## 11. Ce que la preuve de largeur ne mesure pas

L’égalité de largeur un n’est pas une borne de temps total ou de mémoire
physique. La taille du programme, le nombre d’actions instrumentées, les
allocations cumulées, le pic mémoire et la taille de l’obligation sont des
objets de mesure distincts.

Le coût de la découverte, de la constitution, de l’application et des
transports doit être rapporté à la chaîne effectivement exécutée. Il ne faut
pas imposer d’abord l’énumération des `2ⁿ` profils pour définir ce coût. Il ne
faut pas non plus déduire une efficacité générale de la seule non-énumération.

La production des garanties et les données fournies par la famille doivent
être identifiées. Une preuve générique de préservation ne se transforme pas
automatiquement en coût de recherche par instance ; inversement, un accord
qu’une instance doit reconstruire ne doit pas être déclaré gratuit parce
qu’il figure dans son type.

Ce document ne réintroduit ni une cible de résolution de SAT arbitraire ni
une conclusion sur le calcul polynomial universel. Il conserve la portée du
résultat de largeur et situe les coûts en aval, dans un modèle annoncé.

## 12. Carte des résultats et de leur portée

| Résultat | Déclarations de production | Portée à conserver |
| --- | --- | --- |
| Génération depuis le périmètre et persistance ancien/nouveau | `iteratedHistory`, `successorOccurrenceSplit` dans [ConstitutiveGeneration](../RelationalPerimeter/Computation/ConstitutiveGeneration.lean) | Histoire effectivement engendrée et transport exact des occurrences ; pas encore de recherche ou de critère. |
| Formation des occurrences de rôle | `RoleFormationAgreement`, `RoleOpeningOccurrence.formedAt` dans [RoleIndexedProfiles](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/RoleIndexedProfiles.lean) | Formation positive indexée par ce rôle ; une lecture booléenne ne la remplace pas. |
| Production et consommation de l’état suivant | `realizeNextOperationalState`, `nextDiscoveryConsumesProducedProvenance`, `nextDiscoveryConsumesRetainedSearchSeed` dans [ConstitutiveFeedback](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ConstitutiveFeedback.lean) | Provenance causale réelle ; pas de nouveauté informationnelle générale. |
| Tête locale et exécution par ressources | `discover`, `applyStage`, `decompose`, `executeWithReferences` dans [MasterResourceExecution](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/MasterResourceExecution.lean) | Dépendances et ordre des producteurs ; pas une mesure d’instructions machine. |
| Normalisation et autorisation depuis la même chaîne | `ExecutedCausalNormalization.result`, `groupingAuthorization` dans [ExecutedCausalNormalization](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ExecutedCausalNormalization.lean) | Cibles produites et autorisation raccordées ; pas un singleton indépendant. |
| Pleine largeur exactement quand le régime conserve séparément | `class_iff_on_master_carrier`, `class_iff_on_executed_regime` dans [UnifiedPublicCertificate](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean) | Régimes finis surjectifs, même carrier, classe binaire ; pas une borne de coût. |
| Programme succinct avec action démontrée | `compileRoleHistory_atomCount_exact` dans [RoleIndexedProgram](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/RoleIndexedProgram.lean), `publicConstitutiveNormalizerSuccinctness` dans [ConstitutiveNormalizerSuccinctness](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ConstitutiveNormalizerSuccinctness.lean) | Un atome par rôle du programme maître ; théorème d’interprétation sur le domaine propre de l’autre interface publique. Métriques de code, non coût total. |
| Distinction source et regroupement | `distinctPair`, `carry_fibres`, `coDetermination_fibres` dans [UnifiedPublicCertificate](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean) | Deux profils distincts peuvent avoir la même obligation produite. |
| Prolongement historique | `Support.Extension.compose` dans [ConstructedSupport](../RelationalPerimeter/Constitution/Resources/ConstructedSupport.lean), `Instance.grow`, `Growth.resume` dans [UnifiedPublicCertificate](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean) | Références et lectures anciennes conservées dans un support effectivement étendu. |
| Préservation et cohérence des actions de traces | `arbitrary_trace_preserves` dans [UnifiedPublicCertificate](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean), `normalization_coherent` dans [RoleGroupingSemantics](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/RoleGroupingSemantics.lean) | Données arbitraires, même politique, même profil source et même cible normalisante. |
| Limitation d’une lecture état/quantité | `authoritative_instruction_action_not_factors_on_executed_system` dans [ExtensionalOperationalStability](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ExtensionalOperationalStability.lean) | Projection et domaine définis ; pas l’impossibilité de toute représentation. |
| Reprise du moteur réel | `next_exact`, `sourceRun_is_resource_execution` dans [LiveResourceContinuation](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/LiveResourceContinuation.lean) | Même continuation du moteur depuis les matériaux conservés. |
| Exactitude de toutes les requêtes futures du contrat | `all_future_events`, `all_future_reads`, `all_requests_admitted`, `all_requests_reflected` dans [ProducedProfileContinuation](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ProducedProfileContinuation.lean) | Suites finies de `advance` et d’inspections de la cible préparée ; lectures et admissions annoncées via la projection, non consultation de toute l’archive. |
| Irrécupérabilité d’un profil | `memory_fibres`, `profile_not_recoverable` dans [ProducedProfileContinuation](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ProducedProfileContinuation.lean) | À curseur fixé, pas de décodeur uniforme du profil source ; pas l’effacement de toute provenance. |
| Réunion des garanties sur une instance | `facts`, `certificate` dans [UnifiedPublicCertificate](../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean) | Paquet scientifique sur cette instance ; pas mémoire runtime et pas encore agent d’IA. |

## 13. Conclusion et prochaine obligation scientifique

Le projet ne montre pas seulement qu’on peut compter moins d’obligations que
de profils. Il construit la chaîne qui rend ce changement de statut légitime,
fait de ses sorties les conditions de la recherche suivante et raccorde sa
continuation à une mémoire qui peut perdre une distinction source.

La conséquence pour une architecture d’IA n’est pas une promesse générale
d’autonomie. C’est une cible de preuve précise : permettre à un agent de
transformer son organisation et sa mémoire tout en suivant les déterminations
et les garanties qui rendent ses actions admissibles, sur une histoire et un
contrat d’interaction explicitement construits.

Pour fermer cette cible, le prochain résultat devra porter sur une exigence
d’agent concrète, son domaine réel d’interaction et le suivi de cette exigence
dans toute la chaîne. Une nouvelle appellation des objets actuels, une réponse
correcte isolée ou une mémoire simplement plus courte ne suffira pas.
