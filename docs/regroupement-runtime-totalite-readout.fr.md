# Regroupement, runtime, totalité et readout

## Statut et portée

Ce document expose la signification conceptuelle et épistémologique du
regroupement dans le cadre relationnel du dépôt. Il précise son articulation
avec les distinctions constituées, le passage local–global, la mémoire du
runtime, la totalité positive, l'obstruction à la totalisation fermante et le
readout des réels.

Il développe conceptuellement les deux affirmations enregistrées
`GODEL_RELATIONAL_SEQUENTIAL_COMPLETENESS` et
`RUNTIME_EFFECTIVE_CAUCHY_REAL_CORRESPONDENCE`. Leurs formulations canoniques
restent le
[raccord de Gödel, du regroupement et de la complétude séquentielle](godel-regroupement-completude-reels.fr.md)
et la
[correspondance runtime–réel de Cauchy effectif](runtime-real-cauchy-effective-correspondence.fr.md).
Le présent texte les relie sans créer une troisième cible scientifique.

Il distingue systématiquement trois niveaux :

- les constructions déjà formalisées dans le dépôt ;
- la lecture conceptuelle exacte autorisée par ces constructions ;
- la cible plus forte encore requise pour identifier les runtimes relationnels
  aux réels usuels.

Le texte n'ajoute ni nouveau théorème, ni verdict d'originalité, ni audit
indépendant. Il ne remplace pas non plus les énoncés Lean par une interprétation
plus forte qu'eux. Les résultats formels décrits ici ont pour révision
d'évidence `9f48180aa8c2aad43d2bc1cbee7419095d4b43dd`. Leurs revues restent
`reader=pending`, `translation=pending` et `independent=not_recorded`.

## Réponse centrale : que deviennent les distinctions ?

Le regroupement ne détruit pas les distinctions constituées. Il modifie leur
**rôle dans la continuation**.

Avant regroupement, deux occurrences distinctes doivent être suivies comme deux
sources distinctes. Après une action de regroupement effectivement exécutée,
elles peuvent porter une même obligation opérationnelle sans devenir une même
occurrence :

```text
p != q                              identités constituées distinctes

trace_p et trace_q                  chemins causaux propres aux deux sources

target(p) = target(q)               cible opérationnelle commune produite

carry(p) = carry(q)                 obligation suivante regroupée
```

La différence ne disparaît donc pas de l'histoire. Elle cesse seulement, sous
le contrat démontré, d'imposer deux continuations opérationnelles indépendantes.

La formule conceptuelle exacte est :

> Le regroupement transforme une différence qui exigeait deux suivis de source
> en une différence historiquement conservée pouvant porter un futur commun.

Cette transformation n'est autorisée ni par l'égalité des valeurs, ni par
l'égalité des readouts, ni par une décision extérieure. Elle doit être produite
par l'action et justifiée par ses traces.

## Les quatre plans d'une distinction

Le mot « distinction » devient ambigu si l'on ne précise pas le plan auquel il
s'applique. Le cadre en sépare au moins quatre.

| Plan | Question | Ce qui peut changer | Condition exacte |
| --- | --- | --- | --- |
| Constitution | S'agit-il de la même occurrence, de la même position et de la même provenance ? | Rien : les occurrences sources restent distinctes. | Aucune égalité de cible, d'obligation ou de readout ne réécrit deux histoires en une. |
| Causalité | Quelles actions et quelles traces ont produit la cible ? | Plusieurs traces peuvent aboutir à une cible commune. | La cible doit être produite par ces traces ; l'égalité isolée de leurs résultats ne les remplace pas. |
| Obligation | Que faut-il encore accomplir à partir de chaque source ? | Les sources peuvent porter une même obligation. | L'égalité doit être reliée à la codétermination exécutée, pas à une application `carry` arbitrairement constante. |
| Futurs et observation | Quels calculs ultérieurs ou readouts peuvent encore distinguer les états ? | Une projection de runtime peut éventuellement oublier une différence. | Le regroupement seul ne l'autorise pas : un contrat exact doit établir l'identité de tous les futurs concernés. |

Ces plans ne s'effondrent pas les uns dans les autres. En particulier :

```text
même readout
  n'implique pas même cible produite

même cible produite
  n'implique pas à elle seule mêmes futurs

mêmes futurs sous un contrat
  n'implique pas même occurrence historique
```

Le runtime intervient précisément entre la cible commune et les futurs : il
doit installer la cible produite dans la mémoire réellement consommée par la
continuation. Sans ce passage, le regroupement resterait un fait local sans
effet causal sur la suite.

## Une différence change de fonction, pas d'existence

Le devenir d'une distinction est relatif au contrat de continuation.

Une différence peut être :

1. **constitutive**, parce qu'elle distingue deux occurrences et leurs
   provenances ;
2. **causalement active**, parce que les deux occurrences exigent encore deux
   actions ou deux traces séparées ;
3. **opérationnellement regroupée**, lorsque ces traces produisent une même
   obligation ;
4. **mémoriellement inactive**, si aucun futur autorisé par le contrat ne peut
   plus l'utiliser pour produire une différence ;
5. **encore historiquement disponible**, même lorsqu'une projection de runtime
   n'a plus besoin de la conserver.

Il n'existe donc pas un instant où la différence « devient fausse ». Ce qui
change est sa juridiction : elle peut rester vraie pour l'identité et la
provenance tout en cessant d'être pertinente pour le prochain calcul.

Le regroupement peut en outre être partiel. Certaines coordonnées d'un profil
peuvent partager une obligation tandis que d'autres restent séparées. Les
fibres de `carry` décrivent ce régime d'obligations ; elles ne constituent pas
un quotient rétroactif des sources.

## Avant le regroupement : la constitution positive

Une occurrence n'est pas primitivement une valeur dans un ensemble. Elle est
située dans une histoire et porte les relations positives qui l'ont constituée.
Son identité comprend notamment sa position, sa provenance et son raccord à
l'exécution qui l'a produite.

Deux occurrences peuvent donc posséder une même valeur observable tout en
restant distinctes :

```text
histoire constituée
   |-- occurrence p -- provenance p -- trace à produire
   `-- occurrence q -- provenance q -- trace à produire
```

L'égalité éventuelle de leurs valeurs ne dispense pas de construire les deux
traces. Avant toute autorisation, il n'existe aucune raison interne de traiter
leurs charges comme une seule charge.

Cette priorité est essentielle : les différences sont constituées avant que le
regroupement n'établisse ce qu'elles peuvent partager. Si l'on commence par une
cible commune ou par une largeur un, on a déjà supposé le résultat que
l'exécution devait produire.

## Chaîne causale exacte du regroupement

Le regroupement doit respecter l'ordre constitutif suivant :

```text
relations et témoins positifs
  -> occurrences et histoires constituées
  -> contextes reçus
  -> recherche réellement exécutée
  -> relation trouvée
  -> action relationnelle
  -> préservation dirigée du critère
  -> cibles effectivement produites
  -> autorisation extraite de cette même chaîne
  -> codétermination opérationnelle
  -> obligation mémorisée pour la continuation
```

Dans `CriterionPreservingAbsorption`, le témoin local conserve ensemble :

- la sortie exacte de l'action exécutée ;
- l'acceptation positive de cette sortie ;
- la préservation dirigée du critère ;
- le changement effectif de la source ;
- la distinction entre occurrences source et cible.

`ActionProducedOperationalTarget` ne reçoit pas une cible extérieure munie
après coup d'une égalité. Son élimination applique l'action effective. La cible
est donc une production avant d'être une donnée utilisée par les conclusions.

À l'échelle d'une réduction, `ExecutedReductionConstitutiveChain` consomme les
licences dans leur ordre dépendant. `ExecutedCausalNormalization.result` est
obtenu par élimination de cette chaîne exacte. La preuve ne reconstruit pas une
sortie indépendante de celle que l'exécution a fournie.

### Les quatre questions à maintenir à chaque passage

Le même objet peut jouer des rôles différents selon le niveau examiné. Pour ne
pas confondre présence d'un champ et dépendance effective, chaque passage doit
être lu selon quatre questions :

| Lecture | Question appliquée au regroupement |
| --- | --- |
| Formation | Quelles histoires, occurrences, positions et provenances indexent les types ? |
| Exécution | Quelle recherche et quelle action calculent réellement la cible et la ressource mémorisée ? |
| Preuve | Quels témoins de trace, d'acceptation et de préservation sont effectivement consommés par la conclusion ? |
| Transport | Quelles distinctions restent dans l'histoire, lesquelles deviennent une obligation commune et lesquelles une projection de runtime peut oublier sous son contrat ? |

Un témoin simplement stocké ne prouve pas que l'exécution suivante le lit. À
l'inverse, une preuve terminale peut consommer peu de champs tout en appartenant
à une chaîne constitutive qui en transporte davantage. Le document distingue
donc toujours la richesse du carrier, la causalité de l'exécution et les
hypothèses logiquement minimales du théorème considéré.

## Codétermination sans identification

`OperationallyCoDetermined` exprime le noyau positif du regroupement : deux
profils constitués possèdent deux traces exécutées vers une cible commune.

```text
p --trace gauche exécutée--\
                             >-- cible t
q --trace droite exécutée--/
```

Le témoin retient :

- l'autorisation issue de la chaîne causale ;
- la cible commune ;
- la trace gauche ;
- la trace droite ;
- l'exactitude de la cible relativement à chaque production.

Le dépôt obtient alors :

```text
carry(p) = carry(q)
  <-> Nonempty (OperationallyCoDetermined normalization p q)
```

Cette équivalence porte sur les obligations produites par cette normalisation.
Elle ne dit pas que `p = q`, ni que toute égalité de valeurs observées fournit
une codétermination.

Dans l'instance publique actuelle, toutes les cibles normalisées convergent
vers la cible retenue construite par la réduction. La codétermination de tous
les profils est donc une propriété forte de cette construction précise. Il ne
faut pas la présenter comme une loi automatique de toute relation ou de tout
régime arbitraire.

## Le local : une production située

Le local n'est pas seulement « petit » ou « fini ». Il est ce qui est produit
depuis une position déterminée de l'histoire :

```text
occurrence + contexte + recherche + action + cible
```

Un résultat local est positif parce que ses données et ses témoins sont
construits. Il ne devient pas global par agrandissement. Même une cible locale
acceptable ne dit pas encore :

- qu'elle a été installée comme mémoire du pas suivant ;
- que la même règle vaut dans tous les contextes finis autorisés ;
- que les futurs issus de deux sources regroupées sont identiques ;
- que toutes les continuations appartiennent à une clôture déjà achevée.

Ces quatre conclusions requièrent quatre passages distincts.

## Premier axe local–global : composition des rôles

À une profondeur finie donnée, un profil choisit une occurrence pour chaque
rôle constitué :

```text
p = (p_1, p_2, ..., p_n)
```

Une politique locale attribue à chaque rôle son régime d'obligations :

```text
carry_i : occurrence_i -> obligation_i
```

Le régime global de ce profil n'est pas introduit comme un objet indépendant.
Il est le produit dépendant des politiques locales :

```text
carry_global(p)
  = (carry_1(p_1), carry_2(p_2), ..., carry_n(p_n))
```

Le théorème `allLocalPoliciesPreserve_iff_globalPreservation` fixe exactement
la conservation sur cet axe : toutes les politiques locales sont injectives si
et seulement si leur régime produit conserve séparément les profils globaux.

La conséquence conceptuelle est précise. Une distinction locale conservée
reste visible dans le profil d'obligations. Une coordonnée localement regroupée
peut cesser de distinguer deux profils qui ne diffèrent que sur cette
coordonnée, sans égaliser leurs occurrences sources.

Cet axe est **horizontal et synchrone**. Il compose les rôles d'un même préfixe
fini ; il ne produit pas encore la continuation historique suivante.

## Second axe local–global : succession par le runtime

Le second axe est **vertical et séquentiel**. La cible produite aujourd'hui
doit devenir une ressource de l'exécution suivante :

```text
étape n

  sources distinctes
       -> actions et traces
       -> cible regroupée c_n
       -> mémoire vivante M_n contenant la ressource nécessaire
       -> exécution suivante qui lit M_n

étape n+1

  nouvelles productions
       -> nouveau regroupement c_(n+1)
       -> nouvelle mémoire M_(n+1)
```

Le regroupement horizontal ne suffit pas : une cible prouvée mais jamais lue
par le calcul suivant resterait un certificat sans rôle constitutif. Le runtime
vertical ne suffit pas non plus : transporter un état ne justifie pas que
plusieurs charges aient une obligation commune.

Le passage local–global exige leur composition :

```text
codétermination horizontale
  + consommation verticale de la cible produite
  + même contrat sur chaque contexte fini accessible
  = cohérence globale relationnelle
```

Le global n'est donc ni un objet placé au-dessus du local, ni la somme de toutes
les occurrences, ni une perspective qui effacerait leurs positions. Il est la
stabilité de la même loi constitutive à travers les contextes finis qu'elle
engendre.

## Ce que « global » veut dire exactement

Trois conditions sont nécessaires pour parler de globalité dans ce cadre.

### Une même provenance de règle

Les productions locales doivent provenir du même producteur ou d'un producteur
relié par une réalisation exacte. Juxtaposer des réponses compatibles obtenues
indépendamment ne construit pas un comportement global.

### Une même continuité causale

La sortie du pas précédent doit être la ressource lue par le pas suivant. Un
témoin stocké mais jamais consommé ne suffit pas.

### Une stabilité sur tous les futurs finis autorisés

Depuis chaque état accessible, toute liste finie admise doit être gouvernée par
le même contrat de transitions, d'événements et d'observations. Le global est
donc une propriété de tous les prolongements finis, pas leur collection
extensive dans un état terminal.

Cette définition empêche deux confusions :

```text
global != readout global
global != fermeture de toutes les continuations
```

Le readout observe la globalité constituée. La fermeture prétendrait l'avoir
déjà achevée dans le même régime.

## Rôle constitutif du runtime

Le runtime n'est pas un programme abstrait auquel on ajouterait une mémoire.
Il est la mémoire vivante strictement requise par le calcul tel qu'il est
effectivement exécuté. Son exécution est l'évolution de cette mémoire :

```text
mémoire accessible M
  + requête autorisée r
  -> production partagée e
  -> état suivant e.next
  -> événement e.event
  -> observation e.readout
```

L'état suivant, l'événement et le readout doivent être les projections du même
paquet exécuté. Les calculer séparément risquerait de produire trois résultats
compatibles en apparence mais causalement indépendants.

Pour être exact sous un contrat de futurs, un runtime réduit doit satisfaire
trois exigences :

1. **suffisance** : sa mémoire permet d'exécuter tous les futurs autorisés ;
2. **nécessité comportementale** : toute distinction qu'elle conserve est
   révélable par au moins un futur du contrat ;
3. **exécution directe** : les transitions lisent cette mémoire réduite, sans
   rappeler une mémoire riche cachée.

L'oubli est alors relatif, jamais absolu. Une projection peut oublier la
provenance ou une ancienne source pour un contrat donné seulement si cette
différence ne peut plus changer aucune transition, admission, événement ou
observation autorisée par ce contrat.

## Forme forte déjà réalisée par le noyau SAT

À portée fixée et pour des mémoires cohérentes, le noyau live réduit prouve :

```text
projectMemory scope one = projectMemory scope two
  <->
pour toute liste finie de requêtes,
run (projectMemory scope one) = run (projectMemory scope two)
```

La direction de gauche donne la suffisance de la projection. La direction de
droite montre que tous les futurs du contrat déterminent la projection.

`any_exact_realization_retains_projection` ajoute une nécessité indépendante
de l'encodage : toute réalisation exacte du même contrat doit conserver les
distinctions que la projection retient.

Cette minimalité est comportementale et relative au contrat. Elle ne mesure ni
un nombre minimal de bits, ni un coût physique, ni la taille de toute la machine
SAT intégrée. Elle établit que la mémoire exécutée est exactement ce dont ces
futurs ont besoin pour rester distinguables.

## Forme forte désormais obtenue pour le runtime des réels effectifs

Le raccord aux réels réalise cette structure dans une portée précisément
délimitée : l'environnement exécutable contient le producteur et le module,
tandis que la mémoire vivante contient ce que l'exécution suivante lit
directement. Le producteur n'est donc ni un indice invisible du type, ni un
interprète extérieur rappelé après la projection.

La chaîne exécutée possède les propriétés suivantes :

- chaque réponse passe par le même journal ordonné de phases ;
- le readout est projeté de la ressource mémorisée après l'action ;
- une source offerte au regroupement possède son exécution et sa provenance ;
- le regroupement local consomme le code source et son témoin de proximité ;
- le témoin exposé et accepté est transporté depuis la charge normalisée
  effectivement produite, sans second rappel indépendant de la loi de Cauchy ;
- le regroupement fini consomme chaque source retenue dans l'ordre ;
- la sortie regroupée est exécutée comme réponse suivante ;
- le pont riche–réduit transporte exactement les transitions, événements,
  admissions et observations sur toute liste finie ;
- deux sources regroupées de même profondeur ont une même projection publique,
  puis les mêmes futurs normalisés, sans égalité de leurs journaux riches.

Pour un environnement fixé, l'égalité de la mémoire est désormais équivalente
à l'égalité de tous les futurs du contrat :

```text
mémoire gauche = mémoire droite
  <-> mêmes transitions, admissions, événements et observations
      pour toute liste finie de requêtes du contrat
```

Pour une famille exécutée fixée, la projection de l'archive riche satisfait la
même caractérisation bilatérale. Toute autre réalisation exacte de ce contrat
doit conserver les distinctions retenues par cette projection. Le runtime des
réels possède ainsi, dans cette portée, l'analogue de la propriété de mémoire
du noyau SAT : suffisance, nécessité comportementale et exécution directe.

Cette exactitude reste relative au contrat et à l'environnement ou à la famille
fixés. Elle ne mesure pas un nombre minimal de bits, n'établit aucun minimum
physique, ne permet pas de comparer deux producteurs différents par la seule
égalité de leurs mémoires et ne reconstruit pas les histoires ou les
occurrences depuis leur projection.

Le transport historique est lui aussi désormais causalement fermé. Chaque
nouvelle charge agit sur la ressource normalisée du préfixe effectivement
transportée ; elle ne repart pas d'une graine reconstruite. La cible issue de
ce regroupement est installée dans la mémoire, puis la continuation suivante
relit cette même ressource :

```text
préfixe historique normalisé
  -> transport de sa ressource
  -> ajout de la charge fraîche
  -> cible produite
  -> cible installée
  -> continuation qui relit cette cible
```

## Totalité positive : pouvoir produire chaque prochain pas

La globalité reçoit une forme de totalité positive lorsque le producteur est
défini pour toute requête finie autorisée depuis tout état accessible :

```text
pour tout état accessible M
et toute requête finie autorisée r,
perform M r produit un paquet exécuté et un état suivant
```

Cette totalité est une propriété d'action. Elle signifie que le prochain pas
peut toujours être produit sous le contrat. Elle ne signifie pas que tous les
pas futurs sont déjà stockés.

L'ordre exact est :

```text
local
  = un pas situé effectivement produit

global
  = une même loi constitutive stable sur chaque contexte fini accessible

totalité positive
  = cette loi répond effectivement à toute requête finie autorisée
```

Une quantification constructive `pour toute requête, produire une réponse` est
une capacité indexée. Elle n'est pas l'énumération achevée de toutes les
réponses et ne transforme pas les futurs en parties d'un état final.

## Totalisation fermante : absorber la nouveauté dans le même régime

La totalisation fermante ajoute une affirmation que la totalité positive ne
contient pas. Elle prétend qu'une continuation strictement nouvelle peut être
réadmise comme déjà interne au même régime de clôture.

```text
totalité positive
  pouvoir produire chaque prochaine continuation finie

totalisation fermante
  absorber la continuation nouvelle dans une clôture du même régime
```

Dans `CircularPresentation`, `TotalLoop` n'est pas le nom de toute propriété
globale. Il possède une conséquence précise : il contracte les deux pôles de la
différence initiale. `rejectTotalLoop` consomme la provenance positive de cette
différence et rejette cette contraction.

De même, `oneStepAfterPerimeter` produit une continuation strictement nouvelle,
et `oneStepAfterPerimeter_notCircularRefinement` interdit seulement de la
réabsorber comme raffinement circulaire du même régime. Il ne rejette ni cette
continuation, ni son exécution, ni sa cohérence avec le passé.

La séparation fondamentale devient :

```text
fermeture du même régime contractant la différence  rejetée

continuation finie effectivement produite           positive

regroupement d'obligations sous contrat              possible

globalité de tous les futurs finis                   possible
```

Le regroupement n'est donc pas une totalisation miniature. Il ne ramène pas la
nouveauté à l'identité. Il rend compatibles des continuations distinctement
produites tout en laissant l'histoire ouverte à un pas supplémentaire.

## Signification épistémologique

Dans une lecture extensive, connaître un tout peut être compris comme disposer
de ses éléments ou d'une définition qui les fixe déjà. Le cadre relationnel
inverse cette priorité : ce qui autorise une connaissance globale est la
maîtrise reproductible des passages constitutifs.

Connaître une production signifie pouvoir :

- identifier l'occurrence et sa provenance ;
- reproduire la recherche et l'action ;
- vérifier la préservation annoncée ;
- suivre la cible effectivement produite ;
- installer cette cible dans la mémoire suivante ;
- déterminer les futurs permis par le contrat.

Le global est alors une invariance de méthode et de comportement, non une
substance extensive primitive. Il ne surplombe pas les productions locales :
il est ce qu'elles établissent ensemble lorsqu'elles restent cohérentes sous
toute continuation finie autorisée.

Le regroupement apporte une forme précise de connaissance : il ne dit pas que
deux sources sont la même chose, mais qu'une différence entre elles n'exige
plus deux obligations futures dans le régime considéré. La preuve conserve le
passé distinct dont elle autorise le futur commun.

Cette lecture impose aussi un ordre de dépendance :

```text
constitution
  -> exécution
  -> regroupement
  -> mémoire
  -> futurs
  -> readout
```

Remonter cet ordre est illégitime. Un readout égal ne reconstitue pas les
traces ; une largeur un ne produit pas la convergence ; une présentation
numérique cohérente ne prouve pas qu'un runtime l'a constituée.

## Largeur, regroupement et mémoire

La largeur est une lecture quantitative aval. Dans la chaîne publique :

```text
actions exécutées
  -> cibles produites
  -> convergence
  -> codétermination
  -> obligations regroupées
  -> largeur exécutée un
```

La largeur un indique qu'une seule obligation demeure dans l'image du régime.
Elle n'indique pas qu'une seule occurrence a existé, qu'une seule trace a été
exécutée ou que la mémoire complète possède une seule donnée.

Réciproquement, la mémoire ne doit pas être assimilée à cette largeur. Elle
peut devoir conserver des occurrences, des provenances, un journal ou des
témoins nécessaires à des futurs que la simple obligation courante ne décrit
pas. Largeur du régime, taille mémoire, nombre d'opérations et coût physique
restent quatre questions distinctes.

## Readout : observation aval, jamais constitution amont

Le readout projette une ressource déjà produite et mémorisée. Il ne produit ni
l'occurrence, ni la trace, ni le regroupement, ni la cohérence des futurs.

Deux états peuvent avoir le même readout tout en différant par leur histoire ou
par des futurs que ce readout ne montre pas. Pour autoriser leur regroupement
mémoriel, il faut un contrat prouvant l'identité du comportement pertinent, pas
seulement l'égalité de l'observation courante.

Lorsqu'un contrat exact est disponible, le readout peut cependant donner une
lecture extensive légitime de la construction relationnelle :

```text
mémoire relationnelle
  -> exécutions finies cohérentes
  -> observations compatibles
  -> présentation extensive aval
```

L'apparence de continuité n'est alors ni primitive ni arbitraire. Elle est ce
que l'observation peut fidèlement exposer d'une cohérence exécutée. Sans le
théorème d'exactitude reliant les deux niveaux, elle resterait seulement une
apparence.

## Application réalisée aux réels de Cauchy effectifs

Dans la construction formalisée, une demande de précision est une continuation
locale :

```text
mémoire actuelle + précision p
  -> réponse source exécutée
  -> action de regroupement
  -> obligation limite produite
  -> mémoire suivante
  -> approximation dyadique lue en aval
```

Les réponses à différentes précisions sont des occurrences distinctes. Leur
compatibilité numérique ne les identifie pas. Le regroupement doit consommer
leurs ressources et leurs témoins de proximité afin de produire une obligation
limite commune. Le runtime doit ensuite rendre cette obligation disponible à
la continuation suivante.

Le réel relationnel obtenu n'est donc pas une suite de codes prise comme objet
runtime primitif. Il est le comportement global d'un runtime capable de
répondre de façon cohérente à toutes les demandes finies de précision :

```text
runtime relationnel accessible
  -> réponses finies produites
  -> regroupements historiques
  -> mêmes obligations de limite sous le contrat
  -> cohérence de tous les futurs de précision
  -> présentation dyadique par readout
```

À ce niveau, deux runtimes peuvent présenter le même réel sans être la même
occurrence ni posséder la même histoire. Leur équivalence porte effectivement
sur leurs readouts et leurs futurs limites finis, puis se relie dans les deux
sens à l'équivalence de présentations dyadiques effectives. L'identité
historique reste plus fine que cette équivalence réelle.

Le producteur, la cohérence intraterme, le module monotone et la loi de Cauchy
restent des contextes reçus. Le runtime constitue leurs exécutions,
regroupements, mémoires et readouts ; il ne prétend ni produire ces entrées à
partir de rien, ni calculer leurs valeurs à partir de l'obstruction
gödelienne.

## Ce que le raccord actuel établit pour les réels

Le raccord actuel construit une complétude séquentielle effective relativement
à une famille de Cauchy exécutée reçue. Cette famille fournit notamment son
producteur, sa cohérence intraterme, son module avec sa monotonie et sa loi de
Cauchy. Le raccord exécute ensuite la source diagonale, le regroupement et la
réponse limite dans la même architecture historique, puis expose le readout
effectivement mémorisé.

L'orientation effectivement obtenue est donc :

```text
famille de Cauchy effective reçue avec ses lois
  -> exécutions sources constituées
  -> regroupements locaux et finis
  -> réponse limite exécutée
  -> futurs normalisés cohérents
  -> readout limite exact
```

C'est davantage qu'un emballage numérique : les ressources, actions,
consommations et journaux sont explicitement raccordés. Une présentation
dyadique effective reçue produit un runtime canonique, et le readout de ce
runtime redonne exactement chaque approximation de la présentation. Dans
l'autre sens, le passage d'un runtime à sa présentation puis à un runtime
conserve positivement les readouts et les futurs limites finis.

La même correspondance est obtenue avec un carrier de Cauchy effectif muni
d'une approximation calculable, d'un module monotone et d'une loi de Cauchy.
Elle reste cependant numérique et comportementale : elle n'égalise pas les
environnements, les journaux, les ressources ou les occurrences.

Ce résultat ne constitue pas encore tous les réels usuels. Il ne fournit ni
les opérations de corps, ni l'ordre ou l'apartness, ni la densité, ni la
propriété archimédienne, ni la complétude d'ordre. Un futur raccord aux réels
usuels devra partir de ces comportements effectifs, transporter les structures
annoncées et seulement ensuite justifier le readout extensif correspondant.

## Raccord conceptuel avec Gödel

Le raccord avec Gödel porte sur la forme de la totalité, pas sur un calcul
direct de nombres réels par l'énoncé diagonal :

```text
même présentation et même histoire
  |-- branche négative : la clôture du même régime est rejetée
  `-- branche positive : la continuation stricte est produite
                            -> runtime
                            -> regroupements
                            -> futurs finis cohérents
                            -> readout réel
```

Gödel localise l'impossibilité de la fermeture totalisante. Il ne fournit pas
la complétude réelle par contradiction. La branche positive doit construire
elle-même chaque ressource, chaque action de regroupement et chaque transition
de mémoire.

Il ne faut donc pas écrire :

```text
False -> réel
```

La conclusion correcte est structurelle : le même cadre peut rejeter la
fermeture qui contracterait sa différence constitutive tout en réalisant une
globalité ouverte où chaque prochain pas fini reste exécutable et cohérent.

Cette articulation est maintenant réalisée sur le même périmètre et la même
base historique `H1` : la production gödelienne fixe l'histoire et rejette la
fermeture du même régime, tandis que la famille de Cauchy reçue fournit les
données numériques exécutées par la branche positive. Les deux branches sont
raccordées sans faire de `False` un producteur de réel.

## État des obligations du runtime réel

La cible effective actuellement déclarée ferme les obligations suivantes sur
la même chaîne exécutée :

- chaque réponse de précision est calculée depuis une mémoire accessible ;
- chaque cible de regroupement est produite par une action qui consomme ses
  sources effectivement exécutées ;
- la cible produite devient une ressource lue par la transition suivante ;
- les occurrences, journaux et provenances sources restent distincts et
  traçables ;
- tout oubli de données est autorisé par un contrat explicite de futurs ;
- à environnement ou famille fixé, l'égalité de la mémoire réduite équivaut à
  l'égalité des futurs du contrat ;
- toute réalisation exacte du même contrat conserve les distinctions
  comportementales de cette mémoire ;
- l'équivalence des readouts runtime est reliée dans les deux sens à
  l'équivalence des présentations dyadiques effectives et des carriers de
  Cauchy effectifs ;
- le readout est dérivé de l'exécution et n'est jamais utilisé pour constituer
  rétroactivement ses occurrences.

La cible plus large des réels usuels reste ouverte sur les opérations de corps,
l'ordre ou l'apartness, la densité, la propriété archimédienne, la complétude
d'ordre et la fidélité de leur transport par le readout. La couverture de tous
les réels classiques, `AC` et `CH` ne résulte pas de la seule correspondance
effective obtenue ici.

## Conclusion

Le regroupement conserve le passé distinct tout en produisant un futur commun.
Il agit horizontalement sur les obligations de sources constituées ; le runtime
agit verticalement en faisant de la cible produite la mémoire du calcul suivant.

Le global est la cohérence de cette articulation sous toute extension finie
autorisée. La totalité positive est la capacité effective de produire chaque
prochain pas. La totalisation fermante serait l'absorption de toute nouveauté
dans le même régime, avec la contraction que le périmètre interdit. Ces notions
ne sont donc ni synonymes ni des degrés quantitatifs d'un même objet.

Le readout vient en dernier. Il peut exposer une continuité ou un réel sous une
forme extensive seulement parce qu'une chaîne relationnelle a déjà produit,
regroupé, mémorisé et rendu cohérents ses futurs finis.

Dans la portée effective désormais formalisée, la mémoire du runtime est
caractérisée par son contrat de futurs, le regroupement historique transporte
réellement la ressource du préfixe, et les readouts correspondent dans les deux
sens aux présentations et carriers de Cauchy effectifs. Cette fermeture formelle
renforce la lecture conceptuelle sans convertir l'équivalence comportementale
en identité historique ni l'effectivité en totalité des réels classiques.

L'idée directrice peut finalement s'énoncer ainsi :

> La totalité relationnelle n'est pas la possession de toutes les réponses ;
> elle est la capacité, portée par une mémoire exacte, de produire toute
> prochaine réponse finie sans perdre les distinctions constitutives dont le
> futur a encore besoin.

## Repères formels

- `StrongPerimetralTurning.CircularPresentation.rejectTotalLoop`
- `StrongPerimetralTurning.oneStepAfterPerimeterStrict`
- `StrongPerimetralTurning.oneStepAfterPerimeter_notCircularRefinement`
- `ConstitutiveSearch.EndogenousDecomposition.CriterionPreservingAbsorption`
- `ConstitutiveSearch.EndogenousDecomposition.RolewiseObligationPolicy`
- `ConstitutiveSearch.EndogenousDecomposition.allLocalPoliciesPreserve_iff_globalPreservation`
- `ConstitutiveSearch.EndogenousDecomposition.ExecutedReductionConstitutiveChain`
- `ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization`
- `ConstitutiveSearch.EndogenousDecomposition.OperationallyCoDetermined`
- `ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.carry_eq_iff_coDetermined`
- `ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.minimality`
- `ConstitutiveSearch.ReconfigurableMachine.LiveReduction.any_exact_realization_retains_projection`
- `RelationalPerimeter.Constitution.Reals.LocalGrouping.SharedTargetWithoutSourceIdentification`
- `RelationalPerimeter.Constitution.Reals.HistoricalGrouping.advanceBatch`
- `RelationalPerimeter.Constitution.Reals.HistoricalGrouping.BatchAdvance.resultFromTransport`
- `RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.historicalSeed`
- `RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.normalizeHistorical`
- `RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedFiniteGrouping.normalizedBatch_consumed_exact`
- `RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.performGrouping`
- `RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.continueInstalled`
- `RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ExecutedCauchyFamily.completeViaRuntime`
- `RelationalPerimeter.Constitution.Reals.CommonRealRuntime.fixedEnvironmentMinimality`
- `RelationalPerimeter.Constitution.Reals.CommonRealRuntime.archiveRealization`
- `RelationalPerimeter.Constitution.Reals.CommonRealRuntime.archiveMemoryMinimality`
- `RelationalPerimeter.Constitution.Reals.CommonRealRuntime.everyArchiveRealizationNeedsMemory`
- `RelationalPerimeter.Constitution.Reals.CommonRealRuntime.numericalFutureCorrespondence`
- `RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.presentation_roundtrip_readout_exact`
- `RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.runtimeReadoutCorrespondence`
- `RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.limitFutureCorrespondence`
- `RelationalPerimeter.Constitution.Reals.EffectiveCauchyReal.runtimeCarrierCorrespondence`
- `RelationalPerimeter.Constitution.Reals.EffectiveCauchyReal.carrier_runtime_roundtrip_equivalent`
- `StrongPerimetralTurning.GodelRelationalCompleteness.raccord`
- `StrongPerimetralTurning.GodelRelationalCompleteness.globalSameRegimeClosureToEmpty`
- `StrongPerimetralTurning.GodelRealCorrespondence.realizePresentation`
- `StrongPerimetralTurning.GodelRealCorrespondence.realizeCarrier`
