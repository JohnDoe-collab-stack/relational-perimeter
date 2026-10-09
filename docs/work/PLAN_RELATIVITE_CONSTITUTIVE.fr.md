# Plan d'implémentation : génération constitutive du domaine relativiste

## 1. Ce que nous voulons construire

**La cible finale est de démontrer que la constitution relationnelle des
événements et de leurs dépendances, poursuivie par les productions,
transports et regroupements effectivement autorisés, peut générer de
l'intérieur un domaine continu reconstruisant exactement la structure
relativiste. Cette structure ne doit pas être supposée pour définir les
relations qui sont ensuite censées la produire. Les événements sources
restent distincts ; toute différence de parcours qu'une continuation
physique admissible peut révéler doit rester conservée.**

Il ne suffit donc pas de raccorder une exécution à une métrique reçue. Il
faut construire, dans cet ordre, l'organisation des continuations puis le
domaine physique qu'elle permet de reconstruire, et démontrer les lois
d'espace-temps, de mesure et de gravitation annoncées pour ce domaine.
La relativité géométrique sert ensuite de référence de comparaison exacte.
Elle ne fournit pas clandestinement les événements, les voisinages, les
distances ou les admissions de la construction amont.

Le passage du présent à sa continuation, les changements de description et
les regroupements autorisés restent distincts et raccordés par leurs propres
preuves. Une description géométrique exacte n'est pas, à elle seule, une
production d'événements ni une preuve de dynamique gravitationnelle.

Le travail ne consiste pas à renommer des étapes SAT en événements physiques,
ni à dessiner un graphe auquel on ajouterait ensuite une provenance. Il faut
suivre les déterminations constituées depuis les ressources reçues jusqu'aux
effets que les continuations peuvent encore révéler.

La première livraison devra fermer un passage effectif de la constitution
au regroupement, puis une première reconstruction. Un exemple plat peut en
vérifier les lois ; il ne sera pas la cible finale. Construire d'abord toute
une géométrie plate ou courbe puis chercher comment l'étiqueter avec des
rôles inverserait précisément la méthode. Les calculs plats et courbes
préparés dans la version précédente restent des contrôles aval, recensés
dans les sections 12 et 13, et non les entrées de la genèse.

Une première famille courbe exacte sert de témoin et de consommateur des
interfaces générales, non de définition restrictive de la cible. La portée
des théorèmes génériques sera donnée par leurs hypothèses physiques explicites.
Leur réalisation publique devra fermer ces hypothèses sur des données
construites ; elle ne sera pas un contrat abstrait laissé sans instance.
Le choix d'une classe, d'un contrat ou d'une régularité ne pourra transformer
silencieusement la cible en une simple approximation ou en un cas de
géométrie fourni à l'avance. Si la reconstruction exacte visée ne peut être
fermée, ce manque sera déclaré, sans changement de cible.

Ce plan ne modifie pas la [cible scientifique déjà acquise](../conclusion-largeur-exponentielle-conservation-identites.fr.md).
Il ne déclare pas que cette cible démontre déjà une théorie physique. La
question physique nouvelle et ses livraisons sont identifiées ici séparément.

## 2. État de départ et autorisation de ce lot

- Branche inspectée : `relativite`.
- Révision : `466abaa877a7cec778853621e6d677f655895f55`.
- Toolchain : Lean `4.33.1`, sans modification.
- Sources suivies : aucun changement au moment de la rédaction initiale ;
  le sous-lot numérique a depuis ajouté des modules et leurs raccords publics.
- Deux documents explicatifs non suivis existent déjà dans `docs/work/` ;
  ils sont préservés.
- Révision du plan : 8 octobre 2026, à la demande « Corrige le plan », après
  relecture intégrale du projet. Elle raccorde explicitement le chemin
  d'implémentation aux préfixes effectivement produits, aux reprises de
  longueur arbitraire et aux transports historiques existants. Elle précise
  les lois entre prolongement et raffinement, sans changer la cible de la
  section 1 ni annoncer que le domaine relativiste est déjà construit.
  Cette révision est documentaire uniquement. Elle n'autorise pas
  une nouvelle implémentation, un commit, un push, un changement de branche
  ou un audit.
  Les modifications déjà présentes dans le dossier sont préservées.

La demande suivante « tu peux commencer a implementer » autorise le premier
sous-lot local décrit en section 20. Elle n'autorise ni commit, ni push,
ni changement de branche, ni audit extérieur. Les obligations des autres
lots et la cible de la section 1 demeurent inchangées.

Ce fichier est un document de chantier. Il devra être retiré de l'arbre
intégré dans `main`. Les résultats scientifiques définitifs auront leurs
documents canoniques et leurs entrées de registre propres.

## 3. Invariants de méthode

L'ordre de travail reste celui des [instructions du dépôt](../../AGENTS.md)
et de la [procédure scientifique](../methode-de-travail-scientifique.fr.md) :

```text
relations primitives et temoins positifs
  -> ressources, histoires et occurrences constituees
  -> contextes locaux effectivement recus
  -> recherche executee, si une relation est a reconstruire
  -> action trouvee et preservation separee
  -> decomposition autorisee
  -> continuation effective et productions partagees
  -> memoire sous un contrat physique explicite
  -> lectures et raffinements compatibles de ces productions
  -> reconstruction du domaine, de sa continuite et de ses structures
  -> descriptions geometriques et comparaison relativiste exacte
```

Une loi physique primitive est déclarée comme donnée ; elle n'est pas
présentée comme une découverte du chercheur. Réciproquement, une relation
revendiquée comme trouvée doit provenir de la recherche exécutée et être
consommée par l'action et sa justification.

Une loi primitive peut contraindre la structure reconstructible ; elle ne
doit pas contenir cette structure sous un autre nom. Une distance, un cône
défini dans des coordonnées reçues, un atlas ou une connexion reçus ne
deviennent pas des résultats de genèse parce qu'on les range dans une
structure appelée `Relation`. Chaque loi
fera donc l'objet d'un examen de ses données et de ses consommateurs.
Cela n'interdit pas de recevoir des lois de propagation ou des raccords
relationnels locaux : il faut précisément construire ce qu'ils permettent
de reconstruire, sans leur fournir déjà leur domaine géométrique.

Le contrat décrit les continuations permises et leurs effets. Cette
quantification sémantique sur les futurs ne donne pas à une production
présente le droit de consulter une queue future achevée. La production
locale dépend uniquement des ressources déjà reçues ; sa continuation
consomme ses sorties partagées, sans rejouer cette production.

Chaque histoire exécutée est finie, mais sa longueur n'a pas de plafond
global fixé. Un prolongement admissible part du curseur effectivement
produit, conserve les déterminations antérieures par leurs transports et
peut être repris à son tour. La longueur est une lecture de cette histoire,
pas une primitive qui la constitue, une durée physique ou une résolution.
Les preuves porteront sur des longueurs arbitraires et sur toutes les suites
finies du contrat, pas sur une fenêtre de futurs choisie après les résultats.

Pour chaque construction, consigner quatre choses : ses indices de formation,
les données effectivement lues, les obligations consommées par la preuve et
les distinctions conservées par ses passages. Un champ de provenance adjacent
à une valeur libre ne suffit pas.

Ne pas confondre :

- occurrence et valeur lue ;
- événement constitué et coordonnées de sa description ;
- localisation dans l'espace-temps et position spatiale à un instant choisi ;
- égalité d'un objet constitué et accord numérique de ses lectures ;
- dépendance effectivement utilisée et influence physiquement admissible ;
- ordre d'exécution et ordre causal physique ;
- continuation productive et changement réversible de description ;
- composition des transports et indépendance envers le chemin ;
- conservation d'un critère et exactitude de tous les futurs d'un contrat ;
- regroupement d'obligations et identification des événements sources ;
- mémoire minimale sous contrat et géométrie physique minimale ;
- recouvrement de voisinages et accord de localisation ;
- connexité d'une chaîne de regroupements et continuité topologique ;
- complétion de nombres et reconstruction d'un domaine physique ;
- paramètres reçus d'une loi et structures démontrées depuis cette loi.

Les sources Lean restent constructives et exécutables. Les données en `Type`
ne seront pas remplacées par une existence propositionnelle. Chaque nouveau
fichier aura un unique audit axiomatique final. Une hypothèse d'interface ne
comptera jamais comme la réalisation concrète qu'elle demande.

## 4. Ce qui existe et ce qui manque

| Appui inspecté | Ce qu'il fournit | Ce qu'il ne fournit pas encore |
| --- | --- | --- |
| [Quatre fondations](../../StrongPerimetralTurning.lean), avec [rôles résiduels](../../SegmentedResidualRole.lean) et [retournement abstrait](../../AbstractSegmentedTurning.lean) | Relations positives, constitution, histoires, occurrences, distinction ancien/frais et provenance | Interprétation physique de ces relations |
| [Transports exacts](../../ExactTypeTransport.lean) | Deux applications et deux lois de retour point par point | Préservation automatique de l'ordre causal, des horloges ou de la métrique |
| [Références typées](../../RelationalPerimeter/Constitution/Resources/TypedReferences.lean) et [supports construits](../../RelationalPerimeter/Constitution/Resources/ConstructedSupport.lean) | Production depuis des occurrences antérieures et conservation de leurs lectures | Exhaustivité de toutes les dépendances possibles d'une fonction arbitraire |
| [Exécution locale](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/CausalOperationalExecution.lean) et [maître variable](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/VariableMasterExecution.lean) | Productions partagées, suite indexée par leurs sorties, tête complète indépendante de l'horizon futur | Producteurs physiques, invariance par changement d'ordonnancement |
| [Origine du préfixe produit](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/MasterResourceExecution.lean) : `MasterResources.ProducedPrefix` | Raccord au curseur complet effectivement obtenu depuis l'origine, pas seulement à son endpoint | Réalisation de ce raccord pour les producteurs physiques de A1 |
| [Prolongement du maître](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean) : `Instance.grow`, `Growth.resume` | Suffixe de longueur arbitraire exécuté depuis le curseur produit ; références anciennes transportées et reprises composées | Admission physique des instructions et transport du contrat de A4 |
| [Regroupements historiques](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/HistoricalRoleGrouping.lean) | Plongement injectif des anciens profils, transport des traces et raccord des obligations après renormalisation | Exactitude des regroupements pour les horloges et autres effets du contrat physique |
| [Actions sur traces](../../RelationalPerimeter/Constitution/Grouping/ContinuationContract.lean) | Composition et préservation ; cohérence des chemins formulée séparément | Connexion physique ou preuve de courbure |
| [Contrats de futurs](../../RelationalPerimeter/Constitution/Continuation/Behavior.lean) et [réalisations exactes](../../RelationalPerimeter/Constitution/Continuation/Minimality.lean) | Comparaison de toutes les suites finies du contrat, avec admissions et refus | Contrat d'observations physiques et transport entre descriptions différentes |
| [Signatures](../../RelationalPerimeter/Constitution/Continuation/Signature.lean) | Caractérisation exacte lorsque la base finie complète est construite | Base finie de toute théorie physique ou de tout contrat |
| [Projections et clôture](../../RelationalPerimeter/Constitution/Grouping/Projections.lean) | Regroupements autorisés, chemins d'identifications opérationnelles, lois exactes de leurs fibres | Topologie, variété ou continuité physique |
| [Sémantique des regroupements](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/RoleGroupingSemantics.lean) | Actions et cohérence consommées par les normalisations de rôles | Indépendance des effets envers tous les chemins physiques |
| [Obligations effectivement produites](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ExecutedOutputObligations.lean) | Composition des images locales et raccord aux cibles exécutées, avant toute hypothèse de convergence | Reconstruction de l'espace-temps depuis cette composition |
| [Minimalité du moteur réduit](../../RelationalPerimeter/Computation/Machine/ReducedLiveMinimality.lean) | Nécessité comportementale et exactitude sous le contrat du cœur cohérent | Minimalité de tout contrat physique, de la machine SAT combinée ou des octets matériels |

Point précis : `History.OccurrencePrecedes.trichotomy` ordonne totalement les
occurrences d'une histoire. Il ne faut ni supprimer ce résultat, ni le lire
comme un théorème de comparabilité causale de tous les événements physiques.
Les correspondances entre histoires et leurs dépendances sont une obligation
nouvelle, pas une correction des quatre fondations.

Trois objets ne doivent pas être assimilés :

1. **Sources constituées** : événements et chemins avec leurs références,
   formation et provenance. Un regroupement ne prouve pas leur égalité.
2. **Obligations de continuation** : ce que l'action produite autorise à
   poursuivre ensemble sous un contrat. Une réduction mémoire exacte est
   une obligation supplémentaire si des données sont effectivement oubliées.
3. **Domaine physique reconstruit** : localisations dans l'espace-temps,
   relations de voisinage, mesures
   et chemins interprétés. Son lien avec les deux premiers objets demande
   des constructions et des lois spécifiques. Un état minimal de machine
   n'est pas, par définition, un point d'espace-temps.

Les résultats de projections complémentaires montrent qu'une chaîne de
regroupements peut relier des sources que des lectures conjointes distinguent
encore. Ils rendent la question de la continuité précise ; ils ne prouvent
pas déjà que cette chaîne est un continuum lorentzien. De même, le backend
de Cauchy construit des nombres : son existence ne ferme pas la construction
des voisinages physiques ni la couverture du domaine par les productions.

### 4.1 Chemin interne à réemployer, sans reconstruire une fondation

Les constructions suivantes existent dans le maître. Elles sont le point
de départ du raccord, non des noms de nouveaux types à ajouter en parallèle :

| Construction existante | Données effectivement raccordées | Obligation physique à fermer |
| --- | --- | --- |
| `MasterResources.ProducedPrefix` | Origine, histoire exécutée et curseur complet retourné par son producteur | Attester ensemble l'histoire physique et le curseur reçu ; une égalité de frontière seule ne suffit pas |
| `executeCausalOperationalHead` et `executeCausalOperationalExecutionHistory_head_independent` | Production locale complète depuis le préfixe reçu, avant la continuation | Construire la tête physique sans paramètre futur et lui donner la même propriété d'indépendance |
| `resource_history_extension`, `Instance.grow`, `Growth.resume` | Suffixe partagé, curseur atteint et attachement à l'ancien préfixe | Prolonger depuis la sortie reçue, puis reprendre depuis la nouvelle sortie ; ne pas rejouer les producteurs anciens |
| `Historical.embedding_injective`, `Historical.extension`, `Historical.renormalized` | Distinction des anciens profils, transport de leurs traces et normalisation dans l'histoire prolongée | Conserver les occurrences physiques et transporter les regroupements autorisés sans effacer un effet encore révélable |
| `FutureEquivalent` et les réalisations exactes | Toutes les listes finies du contrat, observations, admissions, refus et successeurs | Fermer ces mêmes obligations pour le contrat physique complet fixé en A4 |

Ces déclarations spécialisées au maître ne sont pas déjà des lois physiques.
Réemployer les interfaces génériques de `Constitution` et les constructions
de rôles des fondations ; réaliser les raccords physiques à partir d'elles.
Si une généralisation est nécessaire, identifier précisément la spécialisation
à retirer et conserver le maître comme consommateur inchangé. Ni l'exécution
SAT renommée, ni une seconde fondation, ni un carrier physique libre ne
remplacera ce raccord. Les noms physiques des lots A et R restent proposés,
pas livrés.

Le chemin d'une continuation sera donc :

```text
origine et prefixe effectivement produit
  -> curseur atteint, references et contexte recus
  -> instruction admise sur ces ressources constituees
  -> recherche, action et preservation, si une relation est a reconstruire
  -> autorisation et organisation de continuation produites
  -> paire effet/successeur partagee, recue par la continuation
  -> transport des anciennes determinations et des regroupements autorises
  -> suffixe fini de longueur arbitraire, puis nouvelle reprise
  -> lectures et presentations de ces memes productions
```

Le témoin d'origine sert à raccorder un préfixe déjà stocké ; le runner ne
réexécute pas l'origine pour vérifier cette preuve. De même, `growStored`
parcourt des têtes stockées pour attacher le suffixe : absence de réexécution
des producteurs ne signifie ni absence de parcours, ni coût nul.

Pour un préfixe et tout suffixe admis, fermer la conservation des références,
leur injectivité et leurs lectures, puis la composition de deux reprises.
Le regroupement ne reçoit pas un inverse fictif : c'est la trace et son
autorisation qui sont transportées, avec le raccord de renormalisation.
L'injection historique, le transport exact de description à deux retours
et la réduction dirigée des obligations restent trois passages distincts.
Leurs lois de méthode existent ; leur réalisation sous le contrat physique
et leur raccord aux présentations de R3 restent à construire.

## 5. Organisation future des fichiers

L'arbre ci-dessous décrit la destination du chantier, pas son état livré.
Les outils numériques actuellement construits sont recensés en section 18 ;
les modules physiques et géométriques restent à construire.
La nouvelle couche consommera les interfaces locales,
sans reconstruire une autre fondation ou remplacer l'instance maître.
Ce sera une réalisation physique nouvelle sur les interfaces du cadre, pas
l'instance SAT rebaptisée. Le maître computationnel et sa machine restent
préservés ; aucune propriété physique ne leur sera attribuée par analogie.

```text
RelationalPerimeter/
  Constitution/                    interfaces existantes preservees
  Computation/                     maitre et machine existants preserves
  Relativity/
    Arithmetic/                    outils numeriques existants preserves
    ExactArithmetic.lean           utilitaire neutre, sans geometrie
    Analysis/                      outils analytiques, non domaine physique
    Production/
      PhysicalPrimitives.lean      lois recues, sans metrique ou atlas fourni
      LocalInstructions.lean       entrees explicites, interpretation locale
      ConstitutedEvents.lean       occurrences et provenance des productions
      DependencyPaths.lean         chemins produits et influences admissibles
      IndependentSteps.lean        echange d'etapes et raccords exacts
    Continuation/
      PhysicalContract.lean        demandes et admission depuis les lois locales
      PhysicalEffects.lean         effets de chemins et separateurs futurs
      PrefixExecution.lean        production partagee, sans horizon futur
      DescriptionTransport.lean   interface de transport des contrats
    Grouping/
      DiscoveredRelations.lean     chercheur et autorisations effectivement lues
      FuturePreservation.lean      exactitude et separateurs de chemins
      ComplementaryReadings.lean   lectures, fibres et regroupements compatibles
      ProducedOrganization.lean   organisation consommee par la prochaine etape
    Reconstruction/
      PhysicalPresentations.lean  presentations formees sur les productions
      PresentationAgreement.lean accords et transports de description
      ConstitutiveRefinement.lean resolution et raccords de raffinement
      ConstitutiveCover.lean      contraintes et recouvrements depuis ces raccords
      IntrinsicDomain.lean        localisations coherentes, pas depuis R^4
      PhysicalTopology.lean       voisinages reveles par les sondes admissibles
      PhysicalContinuum.lean      continuite et couverture effectivement prouvees
      LocalCharts.lean            dimension, regularite, cartes et retours
      ReconstructedMetric.lean    causalite, calibration, signature et echelle
      ReconstructedConnection.lean action de chemin et connexion raccordees
      ReconstructedDynamics.lean contraintes et loi physique sur les productions
      ExactReconstruction.lean    adequation, reciproques et portee du domaine
    Geometry/                      interfaces mathematiques generiques seulement
      LorentzData.lean             metrique et domaine en tant qu'interface
      MetricConnection.lean        connexion derivee d'une instance de metrique
      Curvature.lean               calculs generiques, aucun evenement fourni
      FieldEquations.lean          lois physiques explicites, pas leur solution
      FrameTransport.lean          lois generiques de transport
      ChartCovariance.lean         lois generiques de changement de description
    Comparison/
      FlatReference.lean          controle aval, jamais entree constitutive
      PlaneWaveReference.lean     famille courbe de comparaison independante
      ReferenceFieldExecution.lean controles locaux sur ce fond declare
      ReconstructedMeasurements.lean meme production lue dans les deux langages
      ReferenceAgreement.lean     comparaison exacte, pas simple plongement
    PublicCertificate.lean         fermeture de la genese et de ses consommateurs
  Relativity.lean                   surface publique, sans import de tests
Tests/
  Relativity/                      consommateurs et regressions
docs/
  science/                         textes FR/EN et preuves de portee
  work/                            plan temporaire, absent de main a terme
```

Le chemin principal est :

```text
fondations et ressources
  -> lois locales declarees, evenements et chemins produits
  -> contrat physique, admission et effets executables
  -> relations trouvees, transports et regroupements autorises
  -> organisation produite, reutilisee par la continuation
  -> contraintes, raffinements et recouvrements constitutivement justifies
  -> presentations coherentes et domaine intrinseque
  -> topologie, continuite, cartes, metrique et connexion reconstruites
  -> lois dynamiques sur ces memes productions
  -> comparaison exacte avec le domaine relativiste annonce
```

Les étapes peuvent s'entrelacer dans une exécution, mais leurs dépendances
doivent respecter cet ordre. Un raffinement précise une présentation de la
même détermination constituée ; il n'est pas, par définition, une nouvelle
étape causale. Si une mesure supplémentaire est nécessaire, son exécution
prolonge réellement le préfixe, puis un raccord conserve la détermination
antérieure dans la description affinée. Aucun de ces passages ne consulte
une trajectoire future déjà terminée ni ne crée rétroactivement un événement.
Le chercheur n'importe ni son scénario consommateur ni le domaine géométrique
à produire. Le contrat amont ne décide pas l'admission en consultant une
métrique aval.

Les outils `Arithmetic` et `Analysis` peuvent être employés par plusieurs
strates : ils fournissent des opérations, pas des événements ou un espace
physique présupposé. Les interfaces `Geometry` exposent les propriétés à
satisfaire ; leur instance constitutive vient de `Reconstruction`. Un espace
de référence plat ou courbe peut être construit séparément pour comparer
les résultats. Il n'est jamais consommé par `PhysicalPrimitives`,
`PhysicalContract`, la recherche ou `ProducedOrganization`.

Il faudra donc distinguer, dans l'inventaire d'imports, **outil géométrique
générique**, **géométrie reconstruite** et **géométrie de référence**. La
présence d'un fichier dans le bon dossier ne garantit pas cette séparation :
elle doit tenir dans les types, les termes et leurs consommateurs.

Aucune dépendance ascendante depuis les fondations ou le maître vers la
relativité. La constitution des événements ne dépendra pas des coordonnées
choisies pour les lire. Les producteurs physiques consomment les lois locales
et les sorties déjà produites : ne pas recevoir une géométrie achevée ne
signifie pas ignorer les interactions physiques. Une structure reconstruite
à une étape peut guider la suivante uniquement via les raccords prouvés à
l'organisation causale qui l'a produite. L'arithmétique neutre et les
producteurs génériques n'introduiront pas de métrique implicite.

La fermeture des imports de `RelationalPerimeter` fait construire les nouveaux
modules numériques par Lake sans ajout de globs. Les tests sont couverts par
le glob de tests existant. Ce comportement a été vérifié par un build réel ;
chaque fichier doit néanmoins avoir son propre artefact de compilation et
entrer dans l'audit exhaustif. La surface publique, l'inventaire
`scripts/stratification.tsv` et les deux contrôleurs portent des strates
numériques explicites et contraintes. La racine publique a sa strate propre ;
aucun module interne ne peut l'importer. Les couches numériques n'importent
ni le maître ni la machine. Aucun import de tests par la production.

## 6. Lot A0 : fixer les objets et les données physiques

Avant d'écrire les producteurs, fixer les primitives physiques, leur domaine
d'entrée et les continuations qu'elles admettent, sans coordonnées ni métrique
préalables. Les préfixes exécutables sont finis de longueur arbitraire ;
reprendre le chemin interne de la section 4.1 pour leurs prolongements,
puis construire les raffinements compatibles de R3. A0 précisera sur quels
états les instructions sont admises : longueur arbitraire ne signifie pas
que toute instruction est toujours permise. Aucun plafond global d'histoire
ni nombre maximal de reprises n'entrera dans les hypothèses générales.
Un nombre fini d'événements dans un run ne sera présenté ni comme la
continuité reconstruite ni comme une hypothèse de nature fondamentalement
discrète du monde.

Établir un registre de données pour ce modèle :

| Donnée | Statut initial | Obligation |
| --- | --- | --- |
| Ressources initiales et témoins relationnels | Reçus | Formation admissible positive |
| Instructions locales et lois d'interaction | Déclarées | Interprétation exécutable et préservation |
| Unité et calibration des horloges | Déclarées | Accord avec les mesures du modèle |
| Valeurs et événements suivants | Produits | Égalité avec la sortie de l'action exécutée |
| Chemins effectivement utilisés | Produits | Raccord aux références effectivement lues |
| Relations de regroupement | À rechercher | Trace de recherche, action et autorisation |
| Lecteurs localisants et précision instrumentale | À construire depuis les interactions et calibrations déclarées | Attachement constitué, lectures effectives et lois de raffinement ; pas de carte reçue |
| Domaine physique, voisinages, dimension et signature | À reconstruire | Constructions depuis les lois et effets ; hypothèses de régularité explicites |
| Coordonnées et changement de description | Lectures aval à construire | Couverture, fidélité annoncée et lois de transport ; pas d'identité des sources depuis une position |
| Paramètres numériques exécutables | Rationnels exacts pour les premières réalisations | Décisions d'admission construites et accord avec l'interprétation analytique |
| Instruments du premier témoin courbe | Sondes tests idéales, commandes et calibrations déclarées | Lois d'action fermées ; absence de rétroaction explicitement limitée à ce modèle |

Une vitesse normalisée à un peut être un choix d'unités après construction
d'une calibration ; elle n'est pas une conséquence de la profondeur de
l'histoire. Dimension, signature et lois d'Einstein ne sont pas actuellement
dérivées des quatre fondations. Il faut identifier ce qui relève d'une loi
physique reçue et ce que cette loi permet réellement de reconstruire. Si la
dimension ou une régularité sont postulées, le théorème est conditionnel sur
ces paramètres ; leur nécessité n'est pas démontrée.

**Sortie du lot :** une classe de données et de lois non géométriques, avec
son contrat et ses obligations de reconstruction. La classe doit être définie
avant le choix du témoin ; elle ne peut avoir pour hypothèse « possède déjà
un espace-temps reconstruit ». Ses conditions physiques seront fermées sur
une famille non triviale de productions, pas seulement satisfaites par un
espace de référence déguisé. Ce lot comprend une décision de faisabilité :
identifier une première loi intrinsèque candidate et son premier raccord
constructif. La réussite n'est pas présumée.

Cette décision doit aussi identifier les règles locales qui permettraient
de passer des présentations de R3 aux recouvrements de R4. Leurs entrées
seront des interactions, calibrations et raccords admis par ces lois ; elles
ne pourront recevoir « toutes les positions existent » ou « cette région
est déjà une variété » comme hypothèses dissimulées. Une règle mathématique
de recouvrement ne fournit pas à elle seule sa justification physique.

## 7. Lot A1 : constituer les événements par des producteurs locaux

### 7.1 Raccord aux rôles constitutifs relationnels

Instancier les familles relationnelles du cadre avec les exigences locales,
les ressources qui y répondent et les témoins positifs de leurs raccords.
Par exemple, une réception exige la sortie d'une émission déterminée et
un chemin admissible ; son témoin doit porter ce raccord, pas une étiquette
« réception » ajoutée à une valeur libre.

Construire l'objet relationnel initial, les occurrences concernées et leurs
passages historiques avec les interfaces locales. Documenter le raccord
entre ces rôles et chaque référence consommée par un producteur. Une histoire
de ressources générique, sans ce raccord, ne sera pas présentée comme une
instance fermée de la méthode des rôles constitutifs.

Les garanties conditionnelles des fondations ne deviennent pas des lois
physiques universelles. Fermer leurs hypothèses là où la construction les
utilise ; conserver la différence entre une jonction admissible et une
identification des sources.

### 7.2 Instruction, évaluation et formation partagée

Construire une grammaire locale d'instructions interprétées en utilisant les
références typées existantes. Tous les paramètres variables et les ressources
reconnues comme causales seront des entrées explicites de cette grammaire.
L'interprète produira la valeur et son témoignage de formation ensemble.

Pourquoi ce passage est nécessaire : `Producer.operation` est une fonction
générique. Une fermeture peut capturer une donnée qui n'apparaît pas dans ses
ports. La présence de `Ports` ne prouve donc pas seule une localité physique.
La grammaire fermée devra rendre ces captures impossibles dans le modèle,
ou les exposer comme ressources reçues et suivre leur provenance.

Un événement sera constitué par le rôle d'une production effective, avec
ses entrées, sa sortie et ses témoins. Sa référence renverra à cette
constitution, jamais à un identifiant numérique libre. Les numéros utiles
à l'affichage viendront ensuite. Une ressource portée par l'événement possède
sa propre occurrence ; l'égalité de ses valeurs n'identifie ni les ressources
ni leurs événements.

Le runner liera une paire unique contenant l'effet et le support suivant.
La continuation recevra ce support, jamais une reconstruction de la sortie.

Construire aussi le raccord du préfixe produit de la section 4.1 : l'origine,
l'histoire stockée, le support et le curseur retournés doivent être ceux
de cette exécution. Deux curseurs partageant une frontière ne sont pas
interchangeables si leurs ressources ou leur provenance diffèrent.
L'attestation de ce raccord ne doit pas appeler une seconde fois le producteur.

**Preuves attendues :**

- sortie égale à l'interprétation de l'instruction sur ses entrées lues ;
- conservation de chaque ancienne occurrence et distinction de la fraîche ;
- transport des témoins de formation et de provenance ;
- à instruction locale fixée, égalité de la tête produite depuis le même
  préfixe et les mêmes ressources constituées, quels que soient les
  prolongements admissibles ; cette égalité ne confond pas des instructions
  différentes ni deux occurrences distinctes aux valeurs égales ;
- absence de paramètre contenant la continuation terminée ;
- absence de réexécution de la production pour obtenir son second résultat.

La localité ici est d'abord une propriété de dépendance. Elle ne sera appelée
localité physique qu'après son raccord aux influences permises par le modèle.

### 7.3 Rencontres constituées et lectures de position

Séparer dans les types : les occurrences de ressources, les événements
formés par les interactions et la lecture géométrique de leur position.
Une arrivée produit une ressource locale avec son histoire. Une rencontre
consomme les références exactes des arrivées admises et constitue un nouvel
événement d'interaction ; elle ne transforme pas ces références en une même
occurrence.

L'autorisation locale de rencontre doit porter les raccords physiques des
arrivées réellement reçues : propagation ou trajet admis, compatibilité
locale et état des instruments. Elle est construite depuis les productions
présentes, pas depuis la continuation achevée. Une égalité de coordonnées
sera une conséquence à vérifier après reconstruction. Elle ne sert pas
à définir l'admission amont. Une réalisation comparative recevant déjà
des coordonnées doit être identifiée comme telle ; elle ne ferme pas la genèse.

**Obligations :** conserver les références sources et leurs témoins dans
l'interaction, prouver leur distinction lorsque leurs parcours diffèrent,
puis dériver leur présence au lieu de la rencontre depuis les lois du modèle.
Deux événements ou ressources distincts peuvent avoir la même lecture de
position. Un transport exact porte sur les présentations constituées,
pas sur cette seule projection numérique.

## 8. Lot A2 : séparer dépendance utilisée et influence admissible

Construire les chemins de dépendance à partir de la formation et des références
des producteurs, non depuis les positions dans une liste. Un chemin portera
les passages composés et leurs sources et cibles exactes.

Définir séparément les influences admissibles par les lois de signaux et les
extensions autorisées du modèle. Prouver que toute influence effectivement
utilisée est admissible. La réciproque n'est pas automatique : un signal
possible peut ne pas avoir été envoyé.

L'absence de chemin exécuté ne signifiera donc pas séparation spatiale.
Pour affirmer une absence d'influence dans un domaine, construire la réfutation
des chemins admissibles de ce domaine. Si des extensions peuvent ajouter des
liaisons, ne pas généraliser une absence présente à tous les futurs.

**Preuves attendues :** composition des chemins, transport des anciennes
dépendances, absence de cycles de production dans le modèle incrémental et
invariance de la dépendance sous les correspondances construites au lot A3.
L'acyclicité de ce modèle n'est pas une exclusion universelle des courbes
causales fermées en relativité générale.

## 9. Lot A3 : construire plusieurs ordres sans imposer un temps absolu

Deux opérations seront déclarées indépendantes seulement si leurs données
lues et leurs effets permettent effectivement leur échange : aucune ne
consomme la production de l'autre, et leurs modifications partagées sont
compatibles. Une simple absence d'arête affichée ne suffira pas.

Construire les deux ordres d'exécution depuis le même support initial.
Construire ensuite les transports entre leurs occurrences et ressources,
avec conservation des entrées, valeurs, formation et provenance. Étendre
ces correspondances aux continuations concernées.

```text
support initial -> production A -> production B -> continuation
support initial -> production B -> production A -> continuation
```

**Preuves attendues :**

- les deux chemins sont positivement exécutables ;
- leurs occurrences correspondantes restent distinctes ;
- les deux lois de retour des correspondances ;
- conservation des dépendances, pas seulement des valeurs finales ;
- préservation de toutes les observations du contrat transporté ;
- contre-exemple avec une dépendance réelle qui interdit l'échange.

La comparaison des états se fera au même ensemble de productions accomplies.
Entre A et B, les deux ordres n'ont pas accompli les mêmes productions : leurs
frontières intermédiaires ne seront pas artificiellement égalées. L'absence
de temps global privilégié n'autorise pas à effacer cette différence.

## 10. Lot A4 : fixer le contrat d'observations et de continuation

Construire les demandes physiques du modèle : produire une action locale,
émettre ou recevoir un signal, lire une horloge et comparer les résultats
transportés autorisés. Chaque demande aura ses conditions positives
d'admission, son effet, son successeur et son refus éventuel.

Le contrat sera fixé avant toute réduction mémoire. Il devra couvrir les
entrelacements permis des demandes, pas uniquement une trajectoire de
démonstration. Les décisions d'admission seront exécutables sur le domaine
déclaré ; le nombre fini de commandes ne suffit pas à le garantir. Une
décision générale de toute influence future ne sera pas supposée sans
construction.

Les admissions sont définies depuis les lois locales,
les ressources et leurs raccords, sans consulter une métrique ou un cône
de référence. Il faudra prouver ensuite leur accord avec le domaine reconstruit.
Le contrat physique ne sera pas rétréci pour rendre des parcours indiscernables.

Réutiliser `FutureContract` et les lois de réalisation exacte lorsque leurs
domaines conviennent. L'évaluateur exécutable restera à paire partagée ; les
fonctions séparées du contrat seront seulement la spécification de référence.

**Preuves attendues :** accord du runner avec les observations de référence
pour toutes les listes finies, y compris les refus ; stabilité des
correspondances sous une demande ; conservation des effets de chemin qui
peuvent être révélés ensuite.

Un premier consommateur fini pourra fermer cette obligation : instructions physiques
en nombre fini pour un scénario donné, lectures répétées permises ensuite,
et refus précis des actions hors domaine. Les valeurs physiques initiales
peuvent être paramétrées ; cela n'autorise pas de nouvelles interactions
arbitraires qui n'auraient pas été prises en compte dans la preuve.
Ce consommateur n'est qu'intermédiaire. Le contrat de la classe finale doit
permettre les prolongements et les raffinements requis pour reconstruire
le domaine annoncé, avec leurs lois de compatibilité.

### 10.1 Paramètres et décisions du runtime

Pour les premières réalisations plate et courbe, les coefficients et
paramètres reçus sont des rationnels exacts, avec représentation canonique
et opérations prouvées. Les données analytiques réelles interprètent ce
calcul ; elles ne servent pas à décider arbitrairement une égalité ou un
ordre entre suites d'approximation.

| Demande | Décision exécutable à construire | Garantie physique séparée |
| --- | --- | --- |
| Avancer un parcours | Référence vivante, incrément rationnel positif, borne locale respectée | Action du segment conforme aux lois sur tout le segment |
| Émettre ou recevoir | Ports disponibles, émission constituée et raccord local admissible | Propagation et réception conformes au modèle |
| Lire une horloge ou une sonde | Instrument présent et lecture permise à cette frontière | Calibration et accord de cette lecture avec sa réalisation |
| Comparer à une rencontre | Productions d'arrivée présentes et autorisation locale construite | Rencontre et repère commun raccordés aux mêmes productions |

Prouver pour chaque branche que le refus réfute exactement l'admission de
ce contrat, et que l'acceptation construit son témoin positif. La disponibilité
d'un port ou d'un instrument est lue dans l'état constitué, pas dans la liste
des événements futurs. Pour B6, la positivité et les lois de trajet sont
fermées symboliquement pour les commandes admises ; la décision ne tente
pas d'analyser une fonction réelle arbitraire.

Les branches de décision inspectent les constructeurs et références de
l'état local. Les invariants déjà établis fournissent les lois physiques
nécessaires à la branche positive. Il ne suffit pas de demander comme entrée
« un témoin d'admission ou sa réfutation » : le décideur concret construit
cette alternative et ses raccords depuis cet état et les paramètres reçus.

La famille polynomiale exécutable est paramétrée par des coefficients
rationnels, mais les champs et courbes interprétés vivent sur leur domaine
réel. Les interfaces géométriques générales restent distinctes de cette
réalisation concrète. Étendre le runtime à d'autres paramètres exige une
construction de leurs décisions, pas une hypothèse de décidabilité gratuite
ni la suppression de demandes après observation d'un échec.

### 10.2 Exactitude de toutes les suites

Une base finie de tests pourra servir de preuve complète seulement si sa
complétude est construite pour ce contrat, même avec des suites de demandes
de longueur arbitraire. Sinon, utiliser une simulation inductive construite
avec les lois locales. Ne pas remplacer l'une de ces preuves par un test de
quelques suites ou une hypothèse de complétude laissée ouverte.

## 11. Lots R1-R7 : construire le passage du regroupement au domaine

Ces lots sont le centre du plan révisé. Aucun de leurs résultats n'est
actuellement livré. Les noms proposés désignent des obligations à construire,
pas des déclarations existantes. Leurs entrées viennent de A0-A4 ; les
géométries des sections 12 et 13 ne sont pas leurs données d'entrée.

### R1. Recherche, action et organisation de la continuation

**Entrées :** contexte constitué reçu, ressources locales, candidats déclarés,
contrat physique et garanties déjà produites sur les actions primitives.

**Construction :** le même chercheur exécutable retourne un échec ou une
relation, son action, sa trace de recherche et une autorisation effectivement
utilisée. L'organisation suivante est formée depuis le résultat de cette
action. Aucun type d'obligation singleton ni partition attendue n'est fourni
comme résultat du chercheur.

La conservation d'un critère et l'exactitude de tous les futurs sont deux
obligations différentes. Pour le regroupement physique, prouver les lois
locales qui impliquent l'exactitude de toutes les suites du contrat. Le
chercheur peut reconnaître un domaine de relations avec ces certificats ;
il n'a pas à décider l'équivalence de tous les programmes ou à énumérer
tous les futurs.

**Consommateur :** la prochaine production reçoit cette organisation et ses
sorties partagées. Elle ne reconstruit pas indépendamment la relation et ne
rejoue pas la recherche pour obtenir une seconde composante.

**Preuves de fermeture :**

- image opérationnelle exacte : deux sources ont la même obligation si
  et seulement si leurs cibles effectivement produites sont les mêmes ;
- formation des cibles depuis les actions trouvées, avec consommation des
  garanties, pas simple stockage d'un témoin adjacent ;
- source et provenance conservées à travers les transports exacts ;
- même tête produite depuis les mêmes entrées constituées, indépendamment
  du prolongement ; égalité de l'objet produit complet, pas seulement d'une
  projection qui cacherait une dépendance envers la queue ;
- au moins un regroupement autorisé et un refus de regroupement, avec un
  séparateur futur du même contrat, sur des contextes positivement construits ;
- autorisation stable sous les continuations de ce contrat.

Les deux ordres de productions indépendantes de A3 fourniront un premier
cas positif. Des horloges ou sondes de parcours fourniront le cas négatif.
Ces témoins ne remplacent pas les lois génériques. La largeur reste un
readout des obligations : ni espace physique, ni volume, ni temps ne sont
définis par un dénombrement de branches.

### R2. Projections complémentaires et distinctions encore révélables

**Entrées :** productions de R1, contrat physique de A4 et lecteurs admis.
Le contrat complet est fixé avant de sélectionner une projection. Une lecture
partielle peut servir à localiser ou à décrire ; elle n'autorise pas seule
l'oubli des autres effets du contrat.

**Relations à séparer dans les types :**

| Relation | Donnée ou preuve requise | Usage autorisé |
| --- | --- | --- |
| Accord conjoint des projections | Même lecture pour chaque lecteur de la famille fixée | Comparer ce que ces lecteurs révèlent ensemble |
| Chaîne de noyaux de projections | Chaque lien a une projection commune, éventuellement différente du lien précédent | Composer ces liens ; aucune conclusion automatique sur toutes les lectures |
| Jonction opérationnelle autorisée | Deux traces exécutées vers une cible commune et préservation du contrat physique | Poursuivre les obligations ensemble, sans identifier leurs sources |
| Transport exact de description | Applications, retours et traduction des demandes, admissions et effets | Décrire la même détermination dans des présentations différentes |

Cette distinction est déjà visible dans `ProjectionFamily.Path` et
`JointAgreement`. Dans le
[cas de rôles construit](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/CertifiedRoleGrouping.lean),
`joint_injective` distingue les profils par les lectures conjointes lorsque
l'histoire comporte au moins deux rôles, alors que `executed_path` relie
les profils du régime exécuté. Ni l'une ni l'autre de ces relations ne sera
rebaptisée « même point physique » sans le raccord de R3-R4.

**Construction :** pour chaque projection utilisée par le chercheur,
construire l'action qui réalise le lien et sa préservation. Composer ces
actions sur les sorties réellement produites. Si un lien ne préserve qu'un
critère, il reste un regroupement pour ce critère : il ne devient pas une
réduction exacte de la mémoire physique. Un changement de description doit
aussi transporter les demandes ; comparer les mêmes codes bruts dans deux
repères ne suffit pas.

Fermer la préservation du contrat complet pour chaque regroupement physique,
ou garder les données nécessaires aux autres lecteurs. Un élargissement du
contrat exige une nouvelle preuve ; il ne conserve pas gratuitement un ancien
oubli. Une chaîne passant par plusieurs projections ne constitue pas une
preuve d'accord conjoint.

**Preuves :** fibres exactes des cibles, composition des actions et traduction
des lecteurs, séparateurs conjoints et effets de parcours. Deux chemins au
même endpoint peuvent encore être distingués par une horloge ou une sonde
transportée. La cohérence de la normalisation des rôles ne sera pas exportée
comme indépendance de tous les chemins physiques : cela effacerait notamment
des effets de courbure.

**Consommateur :** R3 forme ses présentations sur les productions et raccords
ainsi autorisés. Il ne prend ni les profils bruts ni leurs seules valeurs
comme domaine. Une origine devenue irrécupérable sous le contrat ne devient
pas une source égale à une autre.

### R3. Présentations constituées et raffinements de description

**Entrées :** productions, organisations et transports construits dans
A1-R2, sur les lois de A0 et le contrat fixé en A4. Les noms de types proposés
ci-dessous ne désignent pas des déclarations déjà présentes.

#### R3.1 Former une présentation finie, plutôt que recevoir son carrier

`FinitePresentation` sera une grammaire indexée par le support constitué,
la détermination décrite, le contexte d'instrument et la résolution. La
détermination est référencée par sa formation relationnelle et son histoire,
pas par une position reçue. Les références d'attachement des sondes viennent
des réceptions et rencontres de A1 ; elles ne sont pas des coordonnées.

Les constructeurs publics devront être limités aux passages suivants :

| Passage | Données réellement consommées | Résultat |
| --- | --- | --- |
| Présentation initiale | Ressources reçues, rôle et témoin positif de leur raccord | Première description de la détermination constituée |
| Incorporation d'une production | Paire effet/support produite une seule fois par A1 ou A4 | Description sur le support suivant, avec transport des références antérieures |
| Lecture instrumentale | Instrument attaché, admission et résultat de lecture effectivement produit | Lecture avec sa calibration, sa précision et sa provenance |
| Changement de description | Transport exact de R2 et ses traductions | Nouvelle présentation de la même détermination, avec lois de retour |
| Regroupement autorisé | Action, cibles et autorisation exactes de R1-R2 | Organisation de continuation et lecteurs qui factorisent par elle |

Une présentation peut porter une information partielle, mais pas des valeurs
libres suivies d'une preuve de provenance indépendante. Ses lectures doivent
être celles de ces productions. Un constructeur de présentation ne rejoue
pas une mesure dont il reçoit déjà le résultat partagé.

Séparer ce qui localise une détermination, l'état des instruments et les effets
de parcours. Il s'agit d'une localisation dans l'espace-temps, pas seulement
d'une position spatiale : revenir au même endroit à deux moments différents
ne suffit pas à constituer le même événement. Une mémoire complète n'est pas
une localisation, et deux appareils aux mêmes sorties ne désignent pas
nécessairement la même localisation. Le raccord local vient des interactions
et transports constitués. Cette distinction devra
être prouvée avant de former des cartes en R5.

#### R3.2 Définir l'accord au niveau où il est revendiqué

`DescriptionAgreement` portera un raccord positif entre présentations de la
même détermination transportée, avec traduction des lecteurs et des demandes.
Construire identité, composition et retour des changements exacts. Prouver
l'accord de leurs effets sur toutes les continuations du contrat transporté.
L'accord ne sera ni l'égalité des événements sources, ni l'égalité brute de
deux tuples, ni une simple chaîne de noyaux de projections.

La jonction opérationnelle de R2 reste une construction différente : elle
produit une continuation commune et peut oublier de l'information. Elle ne
reçoit pas de faux inverse. Son passage à une description commune doit
construire l'attachement de cette description, les lecteurs conservés et leur
factorisation par la cible. Une obligation commune ne devient pas à elle
seule un point commun du domaine physique.

Construire une projection `LocalizedPresentation` depuis cette présentation
riche, et les données `AttachedEffects` qui restent attachées à la
détermination localisée : états d'instruments et effets de parcours encore
révélables. Les deux formations doivent consommer les mêmes références et
leurs raccords. La sélection de lectures localisantes doit être justifiée
par ces lois, pas par une suppression arbitraire de champs de mémoire.

`LocationAgreement` comparera ces descriptions de localisation. Sa preuve
vient des attachements et transports constitués, notamment d'une rencontre
effective, jamais de la seule égalité de valeurs d'appareils. Il ne sera pas
indexé par un point géométrique préexistant supposé commun. Il ne sera pas
confondu avec `DescriptionAgreement` sur les présentations riches. Deux
parcours prenant part à la même rencontre peuvent conserver des effets
attachés différents. L'accord de localisation ne donne pas une égalité de
leurs effets ni une autorisation de les oublier.

Les opérations sur les données attachées doivent être raccordées à l'accord
de localisation et aux changements de description autorisés. Un effet
révélable reste disponible au contrat complet, même s'il n'intervient pas
dans une lecture de localisation. Cette séparation n'est donc ni une
réduction du contrat ni une équivalence future indifférenciée de toutes les
mémoires. Elle empêche de transformer chaque état d'appareil ou chaque
parcours en un point supplémentaire d'espace-temps.

#### R3.3 Deux indices distincts : progression causale et résolution

`PhysicalExtension` exécute une instruction admise et constitue son nouvel
événement. `PresentationRefinement` précise une description de la même
détermination et donne sa restriction vers la description moins précise.
Ce sont deux types distincts ; un nombre d'étapes ne servira pas aussi
d'indice de précision.

Un raffinement purement descriptif n'exécute aucune production nouvelle.
Si une sonde supplémentaire est requise, construire d'abord l'extension
physique, puis le transport de l'ancienne détermination et le raffinement
qu'autorise la nouvelle information. L'événement de mesure reste nouveau ;
l'événement décrit n'est pas recréé dans l'ancien préfixe. Le runner présent
n'a jamais une famille de raffinements futurs pour paramètre causal.

Construire les restrictions de précision, leur identité et leur composition,
et prouver qu'elles retrouvent les lectures antérieures avec les garanties
de précision annoncées. Une amélioration d'approximation n'est pas une
égalité de valeurs rationnelles ni un transport réversible de toute donnée.
Une restriction descriptive n'autorise pas seule l'oubli d'une donnée de
runtime : cet oubli demande toujours l'exactitude sous le contrat complet.

Fermer les lois suivantes sur les constructeurs, pas sur des présentations
libres accompagnées après coup de leurs preuves :

1. **Persistance lors du prolongement.** L'injection des occurrences anciennes
   conserve leur formation, leur provenance et leurs lectures déjà produites.
   Transporter la référence de la détermination décrite ; ne pas la recréer
   depuis ses valeurs. Une nouvelle observation peut différer d'une ancienne :
   conserver l'ancienne lecture ne signifie pas figer l'évolution physique.
2. **Composition des reprises.** Deux suffixes effectivement reçus se
   raccordent depuis le curseur intermédiaire ; les transports composés
   retrouvent les mêmes références. Cela ne rend pas égaux deux ordres
   d'instructions différents : leur échange demande la preuve séparée de A3.
3. **Raccord entre prolongement et raffinement.** Pour un raffinement et une
   extension compatibles, construire les deux présentations raccordées de
   la même détermination ancienne : raffinée puis transportée, ou transportée
   puis raffinée. Leurs restrictions doivent donner l'accord de description
   et les garanties de lecture annoncés. Ne pas imposer une égalité brute
   d'encodages, ni déplacer une mesure avant son admission.
4. **Persistance d'une autorisation de regroupement.** Transporter les traces
   exécutées et prouver le raccord de renormalisation sur le support prolongé,
   puis l'exactitude des futurs du même contrat A4. Si une horloge ou un effet
   de parcours permis peut encore distinguer les sources, garder cette
   distinction ; l'égalité des endpoints ne remplace pas cette preuve.
5. **Indépendance envers l'horizon.** L'objet tête complet et ses ressources
   consommées ne dépendent d'aucun suffixe achevé. La quantification sur tous
   les futurs vérifie l'autorisation ; elle n'est jamais une entrée du runner.

Les lois d'extension et de transport prennent pour modèle les constructions
existantes recensées en section 4.1. Le raccord extension/raffinement et la
préservation du contrat physique sont de nouvelles preuves, explicitement
ouvertes tant que leurs constructeurs ne sont pas réalisés. En particulier,
une préservation SAT ne les ferme pas.

Pour deux raffinements compatibles, `CommonRefinement` doit produire un
raffinement commun et ses deux restrictions. Sa compatibilité comprend les
ressources, admissions, lectures et traductions requises. Ne pas postuler que
deux mesures quelconques sont compatibles. Lorsque construire le raffinement
commun demande une production, fermer son admission et ses lois par A1-A4 ;
ne pas demander au théorème le résultat physique manquant comme entrée libre.

**Première fermeture concrète :** sur les primitives candidates de A0,
construire deux ordres indépendants décrivant les mêmes productions accomplies,
leur transport de description, un regroupement autorisé et un parcours encore
séparable. Ajouter deux descriptions à résolutions différentes d'une même
détermination et leur raffinement commun. Montrer séparément qu'une nouvelle
mesure étend l'histoire. Aucun de ces témoins ne suffit seul à reconstruire
le continuum ; ils ferment les constructeurs avant cette extension.
Faire aussi varier les interactions et les lectures admises, avec leurs
garanties de précision et leurs attachements. Raffiner indéfiniment la
description d'une seule détermination ne produit pas à lui seul les autres
localisations d'un domaine continu.

**Consommateur :** R4 utilise ces présentations, accords et restrictions pour
construire ses lectures à la limite et ses voisinages. La loi indépendante
de l'ordonnancement et des labels porte sur ces raccords, pas sur une égalité
artificielle de tous les supports historiques.

| Objet à construire | Formation requise | Consommateur immédiat |
| --- | --- | --- |
| Ressource et occurrence physiques | Rôle primitif, témoin positif et histoire de réception | Producteur local A1 |
| Production locale | Instruction interprétée sur ces ressources exactes | Successeur partagé et recherche R1 |
| Organisation de continuation | Résultat de la relation trouvée, action et autorisation | Prochaine production et constructeurs de présentation |
| Présentation finie | Attachement constitué, productions et lectures incorporées | Accord de description et raffinement R3 |
| Raffinement | Même détermination transportée, restriction et garanties de précision | Contraintes, recouvrements et présentations cohérentes R4 |
| Domaine et structure physique | Construction de R4-R6 sur ces mêmes présentations | Comparaison exacte et certificat R7 |

La dépendance entre organisation et domaine doit être effective : les
constructeurs de présentation et leurs restrictions consomment les raccords
autorisés. Un domaine indépendant accompagné de leur trace ne satisfait pas
R3. Sur un même support, comparer deux organisations admissibles : construire
leurs accords de présentation lorsqu'elles préservent la même détermination,
ou un effet séparateur lorsque le contrat les distingue. Cette obligation
ne force pas une modification logicielle équivalente à changer la géométrie.

### R4. Domaine, voisinages et continuité construits sur ces présentations

Une chaîne finie de regroupements est une connexité de relation ; elle ne
démontre ni continuité topologique ni variété. Compléter des nombres ne
démontre pas que les productions couvrent un domaine physique continu.
Voici le chemin de construction à examiner, et non un résultat déjà fermé.

Le passage retenu pour l'étude est : **contraintes locales constituées,
recouvrements justifiés, puis localisations compatibles à toute précision**.
Il permet d'examiner la formation du domaine sans recevoir d'abord ses points.
Il ne présume ni que ces contraintes suffiront, ni qu'elles donneront une
variété lorentzienne. Les noms proposés dans R4 restent des travaux à réaliser.

#### R4.1 Former les contraintes et leurs recouvrements avant les points

`LocalConstraint` décrira une condition finie de lecture admissible :
instrument et contexte d'attachement issus de R3, calibration, résolution,
plage de lecture et lois de restriction. Ses témoins de satisfaction viennent
des productions riches effectivement reçues. Une description de plage peut
précéder son résultat ; elle ne reçoit pas une position pour fabriquer
ensuite son attachement. Un lecteur refusé n'a pas de valeur fictive.

Pour les lectures numériques construites, utiliser des fenêtres ouvertes à
bords rationnels et des garanties d'erreur positives. Certifier une fenêtre
demande une précision plaçant la lecture strictement entre ses bords, sans
comparaison totale des réels. Les fenêtres décrivent des lectures ; elles
ne constituent ni une grille de positions ni une distance primitive.

Former les conjonctions finies de contraintes avec leurs compatibilités
positives. Leur restriction ou leur raffinement consomme les transports,
traductions et garanties construits en R3. Deux conditions compatibles deux
à deux ne donnent pas gratuitement une réalisation de toute leur famille.
Une conjonction sans réalisation ne sera pas déclarée habitée.

Construire `PhysicalCover` sur cette base, avant tout atlas ou domaine de
points : une contrainte est couverte par une famille de contraintes plus
locales selon les règles autorisées. Fixer des générateurs indexés par des
types explicites ; construire leurs dérivations, puis démontrer identité,
composition et stabilité sous restriction et intersection finie. Chaque
règle génératrice doit avoir sa justification dans A0-R3 : quelles lois,
quelles productions et quelle autorisation permettent ce recouvrement ?
Une relation de couverture libre accompagnée d'une provenance ne suffit pas.

La jonction de R2 intervient par ses cibles et les lecteurs qui factorisent
par son action. Démontrer ce qu'elle permet de transporter entre contraintes
et quelles lectures des effets attachés demeurent nécessaires. Ne pas
déclarer que toute jonction définit automatiquement un voisinage. Cette
consommation doit être visible dans les termes des règles et de leurs lois.

Cette organisation de contraintes et de recouvrements sera construite dans
le projet depuis les raccords de R3. Son nom mathématique ne fournit aucune
règle supplémentaire : chaque générateur consomme les productions et
autorisations qui le justifient. Les propriétés de couverture et d'intersection
sont des obligations aval à démontrer, pas une topologie extérieure donnée
comme solution. Les témoins nécessaires restent en `Type` et exécutables ;
aucune sélection requise ne sera cachée dans une existence propositionnelle.
Une famille de précisions possibles ne signifie pas qu'un run fini les
a toutes exécutées.

**Recouvrement n'est pas identification.** Deux voisinages peuvent se
recouper sans désigner la même localisation ; le recoupement n'est pas
transitif. Prendre sa clôture d'équivalence pourrait identifier toute une
région. Ni cette clôture ni `ProjectionFamily.Path` ne constituent donc
l'accord de localisation. Les chemins de regroupement existants gardent
leurs lois opérationnelles et leur portée propres.

#### R4.2 Construire les localisations cohérentes, pas seulement décrire un événement

`PhysicalPresentation` portera des contraintes compatibles à des précisions
arbitraires, leurs restrictions, les raccords de réalisation admissible et
les moduli des lecteurs numériques. Construire les choix et raffinements
positifs qu'exige le respect des recouvrements. Le passage vers des précisions
plus fines ne reçoit ni point géométrique ni trajectoire future terminée.

Deux constructions doivent être fermées séparément :

1. Une détermination déjà constituée fournit, lorsque les lecteurs sont
   admis, ses descriptions compatibles et leur accord. Ses instruments et
   effets de parcours restent dans la présentation riche de R3.
2. Le domaine continu doit aussi porter les localisations définies par les
   contraintes et leurs raccords de précision, sans exiger que chacune soit
   déjà le nom d'un événement d'un run fini. Chaque approximation admise
   possède une réalisation constitutive compatible ; le passage à la limite
   ne crée pas rétroactivement une occurrence dans une histoire exécutée.

La seconde obligation ne se ferme pas par les raffinements d'une seule
occurrence, ni par l'ajout de suites numériques arbitraires. Construire un
générateur de réalisations compatibles, ou les témoins explicites de la
famille annoncée. « Chaque précision possède une réalisation » sans raccord
entre ces réalisations ne construit pas une famille cohérente. Aucun choix
implicite, oracle ou lecture d'un futur achevé ne comblera ce manque.

Cette quantification sur des familles munies de leurs données de précision
n'exige pas un programme fini énumérant tous les points du continu. Elle
exige leurs raccords constructifs. Les présentations idéales ne deviennent
jamais des paramètres causaux des producteurs physiques locaux.

Les familles constituent une spécification des précisions possibles ; elles
ne signifient pas qu'une exécution finie a effectué une infinité de mesures.
La construction de présentations idéales ne sera pas confondue avec la
succession causale des événements. Si un raffinement demande une mesure,
A1-A4 produisent d'abord cette extension et R3 en conserve les références.

Construire l'accord entre présentations à partir de leurs raccords de
localisation, avec les lois de composition et de restriction. Le domaine
utilise cet accord explicite, sans quotient axiomatique ni choix global de
représentants. Aucun accord n'identifie les occurrences sources. Les actions
doivent respecter l'accord et transporter les effets attachés ; deux
parcours participant à une même rencontre peuvent rester distinguables par
leurs horloges ou par une sonde transportée.

La complétude reste à construire : quand les lectures localisantes autorisées
ne séparent plus deux présentations, produire le raccord annoncé, avec les
hypothèses exactes qui le rendent possible. Ne pas en déduire l'équivalence
des présentations riches ou l'effacement de leurs effets de parcours. Une
famille de lecteurs non séparante ne ferme pas cette obligation.

#### R4.3 Topologie, actions continues et couverture du domaine

Former les ouverts depuis les contraintes et les recouvrements de R4.1,
puis prouver leur interprétation sur les présentations de R4.2. Fermer :

1. couverture des présentations admises et fermeture des intersections
   finies ; la contrainte vide ne suffit pas à séparer les localisations ;
2. invariance sous accord et transport des garanties de précision ; une
   garantie fine n'est pas forcément reconstructible depuis une borne grossière ;
3. voisinages séparateurs pour les distinctions de localisation annoncées,
   sous les hypothèses physiques qui les produisent ; un effet différent
   à une même rencontre ne sépare pas deux localisations ;
4. correspondance entre cette couverture formelle et ses points construits.
   Un système d'ouverts sans points suffisamment nombreux ne démontre pas
   encore le domaine de points requis par la cible relativiste.

Un refus binaire, une égalité exacte ou un seuil avec sa frontière ne sont
pas des ouverts par définition. L'accord, sa négation, la séparation positive
par un lecteur et les propriétés de séparation d'une variété restent distincts.
Les admissions des lecteurs et les traductions d'unités font partie des lois,
pas de conventions effaçant les cas refusés.

Pour chaque effet revendiqué continu, construire l'action sur les
présentations et son transport des recouvrements, avec un contrôle de
précision. Démontrer composition, commutation avec les restrictions et respect
des accords. L'exactitude sur toutes les listes finies du contrat ne fournit
pas seule ces lois de limite. Une action continue sur les seules lectures
de localisation ne justifie pas l'oubli des autres effets physiques.

**Finitude locale, longueur arbitraire.** Les préfixes constitués du projet
ne sont pas, par définition, des partitions discrètes d'un espace déjà donné.
Leur prolongement conserve les déterminations par leurs transports ; leurs
regroupements réorganisent les obligations sans identifier les occurrences.
On ne leur imposera donc ni un horizon fixe ni une topologie de partitions
pour conclure ensuite que le cadre empêche le continu. R4 doit construire
les voisinages depuis leurs contraintes, lecteurs et raccords effectifs.
Inversement, la possibilité de prolonger arbitrairement une histoire ne
démontre pas seule ces lois de continuité ni la couverture relativiste.

Le domaine ne doit ajouter aucune localisation sans raccord constitutif
cohérent. Inversement, R7 doit fournir la présentation de chaque point du
domaine relativiste revendiqué, et les retours au niveau exact annoncé.
Une énumération de réalisations, une plongée dans un espace continu reçu,
ou la seule complétion de nombres ne ferme pas cette couverture.

**Consommateur :** R5 construit dimension, cartes et régularité sur ce même
domaine, puis R6 sa connexion et sa dynamique. Ces structures ne découlent
ni du nom « couverture formelle » ni de fenêtres instrumentales. R7 ferme
la comparaison exacte et les réciproques. Tant que seules des descriptions
finies, des nombres, un système d'ouverts ou une topologie d'observations
sont construits, la cible reste non établie.

### R5. Dimension, cartes, causalité et métrique

**Construction :** obtenir les paramètres de descriptions locales à partir
des mesures admissibles. Construire leurs cartes et leurs retours sur les
domaines annoncés, leur couverture, les raccords entre cartes et la régularité
différentielle requise. Un codage par quatre nombres n'est pas une preuve
de dimension quatre ou de structure localement euclidienne.

L'ordre de dépendance exécutée reste distinct des influences admissibles.
Prouver l'accord de ces influences avec la causalité reconstruite, avec une
réciproque sur le domaine précis des demandes. Ne pas déduire deux liens
opposés de la même coordonnée attribuée à deux occurrences distinctes.

Reconstruire ensuite la métrique depuis les lois de propagation et de
calibration des instruments, avec signature, non-dégénérescence, orientation
et échelle. La causalité seule ne fixe pas cette échelle : deux métriques
reliées par un facteur positif ont les mêmes cônes. Il faut donc un raccord
supplémentaire à des mesures physiques. Les résultats de reconstruction
causale usuels supposent déjà des espaces-temps et des hypothèses de
régularité/causalité ; ils ne prouvent pas que n'importe quelle relation
produite engendre une variété. Voir [Jacobson, §2.4](https://terpconnect.umd.edu/~jacobson/spacetimeprimer.pdf).

**Preuves :** cartes et lois de retour, changement de description des
demandes et observations, fidélité des horloges et signaux, forme lorentzienne
et régularité. Si la dimension ou la signature ont été reçues en A0, le
certificat identifie cette hypothèse et ce qui a réellement été construit ;
il ne les présente pas comme déduites des seules fondations.

**Consommateur :** instance des interfaces géométriques génériques, issue
exactement du domaine de R3-R4. Le choix d'un modèle plat ou courbe de
comparaison intervient seulement ensuite.

### R6. Transport physique, courbure et continuation dynamique

**Entrées :** actions de parcours constituées, effets de R2, domaine et
métrique de R5, lois physiques reçues en A0.

**Construction :** raccorder les transports exécutés à une connexion sur
le domaine reconstruit. Si l'on revendique la connexion de Levi-Civita,
prouver compatibilité métrique et torsion nulle ; ne pas substituer le
calcul d'une connexion depuis une métrique reçue à ce raccord constitutif.
Calculer la courbure et fermer ses contractions sur cette même connexion.

La continuation physique doit poursuivre les champs et instruments depuis
leurs productions locales, et les contraintes doivent rester satisfaites.
La loi gravitationnelle peut être un postulat physique explicite ; il faut
prouver sa réalisation dans les champs reconstruits. Recevoir toute une
solution d'Einstein et la lire pas à pas ne démontre pas sa génération par
le mécanisme constitutif. Le tenseur de matière ne sera pas défini comme
le résidu qui rendrait l'équation vraie par définition.

**Preuves :** action de chemin et loi différentielle raccordées, effets
de parcours séparables, covariance, contraintes préservées, continuation
effective et production partagée. Les sondes tests sans rétroaction seront
identifiées ; elles ne ferment pas la dynamique d'une matière couplée.

**Consommateur :** une réalisation courbe non triviale de ces interfaces.
Le témoin d'ondes de la section 13 contrôle la comparaison géométrique ;
ses coefficients ne deviennent pas, par renommage, une découverte ou une
genèse constitutive. Toute hypothèse nécessaire à la construction générale
sera visible et fermée dans la réalisation annoncée.

### R7. Reconstruction exacte, portée générale et certificat public

Le certificat final doit épingler une seule chaîne : mêmes lois et données
reçues, mêmes ressources, productions, relations trouvées, actions, transports,
regroupements, continuations, lectures et domaine reconstruit. Ni constructeur
privé ni égalité d'une projection ne remplace les lois scientifiques.

**Exactitude requise :**

1. Chaque production et effet annoncé possède son interprétation physique.
2. Chaque point, chemin et observation du domaine revendiqué dispose de sa
   présentation constitutive, ou d'une construction compatible de limite
   lorsque ce domaine l'exige. Couverture et réciproques sont prouvées.
3. Les accords de descriptions ont leurs retours et compositions au niveau
   approprié. Ils ne restaurent pas une information volontairement oubliée
   et n'identifient pas les événements sources.
4. Topologie, régularité, causalité, métrique, calibration, transport,
   courbure et loi dynamique sont préservés par le raccord de comparaison.
5. Les lois génériques quantifient sur la classe fixée en A0 ; une famille
   non triviale ferme positivement leurs hypothèses. Un exemple isolé ou
   une hypothèse de reconstructibilité ne tient pas lieu de cette fermeture.

La comparaison à un domaine de relativité doit annoncer ses hypothèses
globales. Un producteur incrémental acyclique ne couvre pas automatiquement
les espaces-temps à courbes causales fermées ; un domaine de carte ne couvre
pas automatiquement une variété entière. Ces écarts doivent être résolus
ou déclarés ouverts. Restreindre la cible pour les contourner requerrait une
décision explicite de l'utilisateur, pas une réécriture silencieuse du plan.

Les consommateurs publics seront les productions et continuations elles-mêmes,
des lectures physiques et des comparaisons complètes. Les cas plats, courbes,
regroupants et séparables doivent provenir des mêmes interfaces. Le certificat
doit montrer où le regroupement intervient dans la construction du domaine,
et pas seulement que deux états d'une géométrie reçue peuvent être fusionnés.

La phrase « trop d'états pour représenter l'espace » ne sera autorisée que
relativement à des lectures fixées et à une réalisation exacte : distinguer
les états qu'un futur sépare de ceux que l'organisation produite peut ne plus
porter séparément. Une minimalité comportementale ne signifie pas minimum
d'octets ou de surface matérielle, et ne se généralise pas aux descriptions
de toute la physique sans preuve.

## 12. Contrôle aval A5-A8 : cas plat et changements de description

Cette section conserve le premier témoin précis. Son espace de référence
est déclaré ; il vérifie des raccords et des lois, mais ne ferme pas R3-R7.
Les producteurs de la genèse ne reçoivent pas sa métrique ni son tableau.

### A5.1 Arithmétique et domaine de référence

Choisir une arithmétique rationnelle exécutable auditée, avec égalité
décidable et opérations exactes. Vérifier d'abord les déclarations disponibles
dans la toolchain ; sinon, construire la représentation locale nécessaire.
Pas d'import automatique d'une analyse classique pour contourner les règles.

Convention du premier modèle, après choix d'unités :

```text
intervalleCarre(dt, dx) = dt * dt - dx * dx
coneFutur(dt, dx)       = dt >= 0 et dt >= abs(dx)
```

Un intervalle carré n'est pas déjà une durée propre. Les premiers trajets
avec durée propre rationnelle auront un témoin positif de cette durée.
Les trajets généraux demandant une racine ou une intégration appartiendront
à une obligation analytique ultérieure explicitement ouverte.

### A5.2 Raccord aux événements

Les coordonnées seront des lectures des événements déjà produits. La
réalisation devra préserver leurs chemins admissibles. Pour une équivalence
entre influence et relation géométrique, prouver aussi la direction inverse
sur le domaine exact des événements et demandes annoncés.

Cette réciproque ne sera pas exigée du seul cône sur une projection de
position non injective : deux productions au même lieu peuvent rester
distinctes et ordonnées constitutivement. La seule égalité de position ne
fournit donc pas deux dépendances opposées entre elles. Une réflexion des
influences doit conserver les rôles et les admissions de la présentation,
avec un énoncé précis ; aucun iff universel sur les seules coordonnées
ne sera supposé.

Une application dans un espace de coordonnées ne sera pas dite transport
exact vers tout cet espace. Ses lois de retour porteront sur son image
effectivement construite, ou sur deux présentations du même domaine constitué.
La distinction des événements devra être préservée lorsque la réalisation
est revendiquée comme fidèle : la présentation géométrique complète conserve
les références constituées, leurs rôles et leurs raccords. La lecture de
position seule peut prendre la même valeur sur des événements distincts ;
elle n'est donc pas une bijection vers les coordonnées. Les retours exacts
et les lois de provenance portent sur ces présentations complètes, tandis
que la projection de position satisfait ses propres lois physiques.

### A5.3 Premier scénario complet

Construire une émission initiale, deux productions latérales indépendantes
et une réception commune. Les distances, délais locaux et calibrations sont
des entrées déclarées. Les propagations et réceptions utilisent les signaux
effectivement produits. La réception commune consomme les deux arrivées.

Lectures géométriques attendues, dérivées de ces actions dans cette réalisation :

```text
origine             (0, 0)
production A        (5, 3)
production B        (5, -3)
reception commune   (10, 0)
```

Ce tableau n'est pas l'entrée qui fabrique les témoins. Par exemple, une
propagation lumineuse de trois unités suivie de deux unités d'attente locale
peut fournir chaque première arrivée ; les raccords suivants seront construits
avec le même soin. Les événements intermédiaires des signaux restent dans la
construction, même si la synthèse affiche seulement quatre événements.

Construire aussi des trajets d'horloges entre l'origine et la réception :
un trajet droit donne dix unités de temps propre ; les deux segments de
déplacement `(5, 3)` puis `(5, -3)` donnent quatre puis quatre. L'accord
avec la métrique du modèle est à prouver, pas à ajouter comme étiquette.
Ces horloges peuvent comparer leurs lectures lors de la réception commune.
Ce sont des trajets propres à des observateurs, distincts du trajet lumineux
suivi d'une attente qui peut produire un signal au même événement. Le modèle
doit les construire séparément et raccorder positivement leurs rencontres ;
il ne doit pas attribuer quatre unités à une horloge qui n'aurait accompli
que deux unités d'attente après un signal lumineux.

**Sortie du lot :** une réalisation plate concrète, avec production locale,
signaux, deux ordres indépendants et un séparateur de trajets par les horloges.

### A6. Changer de description sans changer la production

Construire les transformations et leur inverse. Pour le premier exemple :

```text
t' = (5 * t - 4 * x) / 3
x' = (5 * x - 4 * t) / 3
```

La transformation inverse change le signe des termes croisés. Prouver les
deux retours, la conservation de l'intervalle carré et de l'orientation du
cône futur. Construire les lois pour la famille rationnelle de coefficients
`a, b` telle que `a * a - b * b = 1` et `a > 0`, pas seulement pour ces nombres.

Les temps coordonnés des productions A et B deviennent `13/3` et `37/3`.
Avec le changement opposé, leur ordre est inversé. Leur absence de lien
causal mutuel sur le domaine annoncé et leurs relations aux émissions et
réceptions doivent rester conservées.

Transporter également les demandes, admissions, effets et observations. Une
lecture de coordonnées change de valeur : exiger son égalité brute entre
descriptions serait une erreur. Construire une loi d'accord après le
changement approprié de description, pour toutes les continuations du contrat.

Les lois existantes de `ExactRealization` utilisent les mêmes types de demandes
et de réponses. Si cela ne convient pas, construire une interface indexée de
transport des contrats, sans affaiblir l'interface existante. Il faut transporter
les lecteurs et les demandes autant que les états.

Un changement de description d'un même observateur n'est pas le remplacement
de celui-ci par une autre horloge suivant un autre trajet. Les effets
physiques différents de ces trajets ne seront pas annulés par covariance.

### A7. Contrôle physique des regroupements de R1-R2

Le contrat intrinsèque et le chercheur de R1-R2 sont construits avant cette
comparaison. Leur raccord aux mesures du cas plat doit être prouvé. La
métrique de référence ne décide pas rétroactivement leurs autorisations.

Pour réduire la mémoire sans changer la computation, construire une
réalisation exacte du contrat complet concerné. La préservation d'un seul
critère ne suffit pas à cette exactitude. Ne pas présenter la capacité à
décider tous les futurs d'une théorie générale comme acquise : le premier
chercheur est limité au domaine dont la complétude peut être prouvée.

Deux cas sont obligatoires :

1. Deux présentations ne différant que par l'ordre de productions prouvées
   indépendantes admettent le raccord et, si le contrat le permet, un état
   de continuation commun, sans identification de leurs occurrences sources.
2. Deux trajets ayant les mêmes extrémités mais des lectures d'horloge
   différentes restent distinguables. Une demande future concrète révèle
   leur différence ; le chercheur ne doit pas autoriser son élimination.

Dans le premier cas, fermer cette autorisation pour les présentations du
scénario construit, au lieu de laisser « si le contrat le permet » comme
une hypothèse externe du certificat. Dans le second, le séparateur doit
être une demande de ce même contrat, pas d'un contrat enrichi après coup.

Le regroupement sera réalisé depuis les effets produits, avec accord exact
des fibres. L'obligation ne sera pas un type singleton fourni à l'avance.
La recherche et l'action suivantes utiliseront les sorties partagées.

La largeur opérationnelle restera une lecture des obligations constituées.
Elle ne sera ni une distance spatiale, ni une mesure de volume, ni une
définition du temps physique. Aucun théorème sur `2^n` ne remplacera les
obligations de ce lot.

### A8. Certificat comparatif intermédiaire et consommateurs

Le certificat comparatif devra assembler les objets effectivement retournés par
un seul scénario exécutable. Il exposera :

- formation des événements et provenance des ressources ;
- tête locale, continuation sur les sorties et partage des productions ;
- transports entre les deux ordres indépendants ;
- réalisation géométrique et portée de sa fidélité ;
- changements de description et invariants ;
- contrat transporté, exactitude des futurs et refus ;
- relation effectivement trouvée, action et garantie de regroupement ;
- séparateur de trajets dont la différence doit rester observable.

Ses égalités doivent épingler ces données, non une reconstruction indépendante
ayant les mêmes lectures. La protection d'un constructeur ne remplacera pas
les lois scientifiques. Les consommateurs importeront uniquement la surface
publique ; les noms de tests ne seront pas des dépendances de production.

Le texte autorisé après fermeture sera : une réalisation relativiste plate
de productions constituées et de continuations exactes, avec changements de
description et regroupements limités par les effets futurs. Il ne dira pas
que la gravitation ou la métrique ont été déduites des seules relations primitives.

## 13. Contrôle aval B0-B9 : outils analytiques et témoin gravitationnel

Les prérequis numériques déjà construits sont recensés en section 18.
Les autres objets et énoncés de cette partie restent à construire. Cette
section conserve les calculs précis de l'ancien plan comme obligations
mathématiques et témoins comparatifs. B1-B9 ne fournissent pas les primitives
de A0-R2 et ne remplacent pas la reconstruction R3-R7. Une solution courbe
exacte reçue sert de référence : elle ne démontre pas sa propre genèse.

### B0. Fermer la faisabilité analytique avant le développement long

**Modules :** `ExactArithmetic`, `PolynomialCalculus`, `ConstructiveContinuum`,
`ReadoutInterpretation`.
Développer selon les besoins des raccords R3-R6. Avant un long développement
analytique, examiner la faisabilité intrinsèque de A0-R3 : un backend numérique
complet ne résoudrait pas l'absence de construction du domaine physique.

Construire un noyau fini pour les rationnels, polynômes multivariés, matrices
de dimension fixée, dérivées et primitives polynomiales. Leurs lois seront
prouvées composante par composante, sans axiome d'extensionnalité. Les fonctions
à valeurs numériques restent exécutables ; aucune table de nombres calculée
hors Lean ne servira de preuve de leurs identités.

Le second raccord est analytique : interpréter ces polynômes sur un domaine
réel constructif, avec opérations, ordre et régularité justifiés. Examiner
une représentation par suites rationnelles munies de modules d'approximation.
Les opérations doivent porter leurs lois d'équivalence ; ne pas introduire
un quotient axiomatique pour rendre leurs représentants égaux. Si le calcul
emploie un setoïde, exposer sa relation et vérifier tous les transports.

#### B0.1 Trois égalités, trois obligations

Une occurrence porte une détermination constituée dans une histoire de rôles.
Sa persistance entre strates se démontre par les transports de cette même
détermination et leurs lois ; elle n'est ni l'égalité de deux types, ni
l'égalité des seules valeurs lues. Lorsqu'une égalité d'occurrences est
revendiquée, elle porte sur les occurrences elles-mêmes, dans leurs indices
constitués ou après le transport justifié de ces indices.
Le runtime emploie l'égalité de ses données exactes normalisées. L'accord
analytique des représentations réelles est une relation d'équivalence explicite
sur leurs lectures, pas une preuve que leurs encodages sont égaux en Lean.
Par exemple, une suite constamment nulle et une suite rationnelle convergeant
vers zéro peuvent représenter la même valeur sans être la même suite.

Construire `ReadoutInterpretation` avec : injection des rationnels exacts,
respect des opérations et dérivées utilisées, réflexion de l'égalité sur
ces rationnels et accord des lectures analytiques. Les preuves portant sur
les occurrences ne sont pas affaiblies en un accord numérique.

`FutureContract` et `ExactRealization` existants restent inchangés. Les
premiers runtimes utilisent leurs réponses exactes ; leurs observations
analytiques sont obtenues par l'interprétation prouvée. Si une interface
physique générique compare directement des observations réelles, construire
une interface distincte dans `DescriptionTransport`, indexée par la relation
d'accord choisie. Elle doit préserver séparément demandes, admissions,
effets, observations et successeurs, par toutes les suites finies. Les
changements de description ont des lois de retour et de composition selon
les relations annoncées ; ils ne donnent pas l'égalité des encodages réels.

Ni cette interface analytique ni ses preuves ne sont une réduction mémoire
de la source. Pour le contrat concret, démontrer l'exactitude avec ses réponses
exactes d'abord, puis l'accord de leur interprétation. Ne pas utiliser un
accord plus faible pour faire disparaître une différence que le contrat
concret permet de lire.

**Obligations de sortie :**

- interprétation de l'évaluation, du produit, de la dérivée et de la primitive ;
- compatibilité avec l'égalité exacte et les représentations équivalentes ;
- régularité des champs polynomiaux et des trajectoires retenues ;
- incarnation de la carte en quatre dimensions, pas seulement des points
  rationnels d'une grille ;
- calcul rationnel exact pour les lectures rationnelles du premier scénario ;
- pont entre l'égalité des lectures exactes et l'accord de leurs réalisations ;
- comparaisons rationnelles qui serviront aux gardes de A4, sans comparaison
  générale de réels ; A4 ferme ensuite leur composition avec les états locaux ;
- client numérique distinguant équivalence analytique et égalité des encodages.

Le client qui combine ce dernier accord avec deux occurrences sources
distinctes sera construit dans `Tests/Relativity` après A1. Il consomme
l'analyse et la production ; il ne crée pas un import de production dans
le noyau analytique. B9 exige ce consommateur et les décisions complètes de
A4. Le contrôle préalable B0 ferme les outils numériques et leur faisabilité,
pas un runtime physique qui n'est pas encore construit. Même fermé, B0
ne démontre pas la continuité physique de R4 : celle-ci doit provenir
des raffinements et regroupements admissibles, pas des nombres seuls.

Un noyau polynomial sur les rationnels ne ferme pas à lui seul le raccord à
une géométrie différentielle réelle. Si ce pont analytique bloque sous les
règles du dépôt, identifier le lemme manquant et suspendre la revendication
physique correspondante. Ne pas attendre un prototype plat complet pour
découvrir ce blocage. Les identités symboliques restent des étapes utiles,
mais ne deviennent pas une preuve d'existence de toute solution d'Einstein.

### B1. Choisir une première famille courbe exacte et ses données reçues

**Modules :** `Geometry/LorentzData`, `Comparison/PlaneWaveReference`,
puis leurs consommateurs.
Le choix de témoin est une famille d'ondes planes de vide, en quatre dimensions,
avec profils polynomiaux. Ce choix rend les calculs exacts explicites ; il ne
limite pas les interfaces générales de gravitation à cette seule famille.
Ce lot fixe d'abord ce choix et ses données. Le module concret
`Comparison/PlaneWaveReference` sera écrit après les outils génériques de B2-B3 ; ceux-ci
ne l'importeront pas. Les lois propres à la famille seront prouvées dans ce
module, en consommant les constructions génériques, sans cycle d'imports.

Dans une carte `(u, v, x, y)`, fixer la convention `(+---)` :

```text
H(u,x,y) = A(u) * (x*x - y*y) + 2 * B(u) * x*y
ds2      = 2*du*dv - dx*dx - dy*dy + H*du*du
```

La théorie géométrique connaît des familles d'ondes planes exactes dont les
deux profils satisfont la condition de vide, et non seulement une approximation
linéarisée. C'est un témoin de contrôle connu, pas une découverte physique
attribuée au projet. Les conventions de signe et de facteur seront recalculées
localement. [Tong, section 5.2.3](https://davidtong.org/pdfs/teaching/general-relativity/gr.pdf).

Déclarer séparément : dimension, unités, loi gravitationnelle, coefficients
initiaux des profils, règles d'évolution de ces coefficients, calibrations
et lois des sondes. Les coefficients ne sont pas des relations découvertes
par notre chercheur. La réception et l'utilisation de ces données doivent
être indexées par les ressources et témoins constitutifs du cadre.
Cette exécution sur fond déclaré est un contrôle comparatif, pas la
réalisation des primitives intrinsèques de A0. La construction R6 devra
expliquer son propre raccord à ce fond, sans le recevoir comme solution.

Premier cas courbe à fermer : `A(u) = 1 + u`, `B(u) = 0`, sur le domaine du
scénario. Le cas `A = B = 0` servira de contrôle plat sur la même interface.
Construire également les lois de la famille entière de profils polynomiaux,
pas seulement une assertion portant sur les valeurs du premier cas.
Les lois géométriques sont génériques sur les coefficients du domaine
analytique construit. Le générateur exécutable de A4 est, lui, réalisé sur
les coefficients rationnels exacts. Distinguer ces deux quantifications :
la première ne fournit pas un décideur pour des entrées réelles arbitraires,
la seconde ne restreint pas les énoncés géométriques génériques.

**Fermeture :** données initiales positives, domaine annoncé, lecture des
profils depuis leur générateur et distinction entre loi donnée et sortie
produite. Une fonction recevant la trajectoire terminée n'est pas ce générateur.

### B2. Construire la métrique et sa connexion, pas deux objets adjacents

**Modules :** `LorentzData`, `MetricConnection`.

À partir de `H` réellement lu, construire la matrice métrique et son inverse :

```text
g      = [[H,1,0,0], [1,0,0,0], [0,0,-1,0], [0,0,0,-1]]
gInv   = [[0,1,0,0], [1,-H,0,0], [0,0,-1,0], [0,0,0,-1]]
```

Prouver symétrie, deux lois d'inverse, non-dégénérescence et signature. Un
repère explicite permet d'établir la signature sans supposer un calcul spectral :
`e0 = E_u + (1-H)/2 * E_v`, `e3 = E_u - (1+H)/2 * E_v`, avec les deux vecteurs
transverses. `E_u` et `E_v` sont les vecteurs de base de la carte ; les
covecteurs différentiels restent des objets de types distincts.

Construire ensuite les coefficients de connexion depuis `gInv` et les dérivées
de `g`. Prouver absence de torsion et compatibilité métrique. Les coefficients
ne seront pas fournis indépendamment pour faire passer une vérification.
L'interface générique accepte une métrique au moins trois fois continûment
différentiable sur son domaine et non dégénérée ; la famille publique ferme
ces obligations par B0 et la construction ci-dessus.

L'orientation future sera une donnée construite, avec un vecteur temporel
positif. Les chemins réellement exécutés seront raccordés à leur admissibilité
par le modèle, sans identifier cet ordre physique à l'ordre de la liste Lean.

La calibration reste distincte de l'ordre causal : celui-ci ne suffit pas à
fixer l'échelle métrique. [Jacobson, section 2.4](https://terpconnect.umd.edu/~jacobson/spacetimeprimer.pdf).
Le passage d'un ensemble d'événements à une géométrie continue exige ses propres
hypothèses et preuves. [Surya, section 2](https://arxiv.org/html/1903.11544v2).

**Fermeture :** métrique et connexion dérivées des mêmes données, lois locales
prouvées et réalisation analytique fermée ; une matrice inversible seule ne suffit pas.

### B3. Calculer la courbure et fermer les équations physiques

**Modules :** `Geometry/Curvature`, `Geometry/FieldEquations`,
`Comparison/PlaneWaveReference`.

Construire le tenseur de courbure depuis la connexion de B2, puis ses
contractions de Ricci, scalaire et d'Einstein. Figer une convention de signes
avant les calculs. Conserver une preuve de chaque définition calculée, au lieu
de fournir les tenseurs attendus sous forme de champs libres.

**Obligations :**

- lois de la dérivation covariante nécessaires et identités de courbure ;
- courbure non nulle lorsque la valeur d'au moins un profil est non nulle au
  point retenu ; ne pas confondre cela avec un profil non nul ailleurs ;
- Ricci nul pour la famille d'ondes construite, malgré cette courbure non nulle ;
- équation `Einstein(g) + Lambda*g = kappa*T` sur le domaine annoncé ;
- transport de cette équation entre les descriptions admissibles.

Le témoin public de vide fixe `T = 0` et `Lambda = 0` indépendamment du calcul
de courbure, puis prouve l'équation. Ne pas définir `T` comme le résidu qui
rendrait cette équation vraie. Les lois de matière des interfaces génériques
doivent rester identifiées ; le témoin de vide ne sera pas présenté comme une
construction de toutes les interactions avec la matière.

Le premier scénario de mesure est celui de sondes tests idéales sur ce fond
de vide : horloges, vecteurs sondés et commandes de parcours n'ajoutent pas
de source au tenseur `T` du modèle réalisé. C'est une hypothèse physique
déclarée avant les preuves, pas une conséquence d'un regroupement ou d'un
oubli mémoire. Les lois et sorties des instruments restent effectivement
construites et consommées ; seule leur rétroaction gravitationnelle est
exclue de cette première réalisation.

Le certificat doit porter ce statut de fond et d'instruments. Si l'on veut
réaliser leur rétroaction, ouvrir un lot matière avec sources indépendamment
définies, lois d'interaction, contraintes et équations couplées fermées.
Ce lot ne sera pas déclaré couvert par le témoin de vide ; il ne peut pas
être supprimé si une revendication finale le requiert. La cible constitutive
générale n'est pas remplacée par l'approximation de sondes tests.

Une dépendance envers le chemin n'est pas, à elle seule, une preuve de
courbure gravitationnelle. Le raccord exige la même connexion, la même métrique
et leurs équations. [Tong, sections 3.2.3, 3.3.3 et 4](https://davidtong.org/pdfs/teaching/general-relativity/gr.pdf).

**Fermeture :** résultat non trivial et équations calculées, sans hypothèse
ouverte d'Einstein stockée dans le certificat de l'instance.

### B4. Contrôle d'une production locale sur le fond de référence

**Module :** `Comparison/ReferenceFieldExecution`, consommant les interfaces
locales, les outils géométriques et le fond de référence.

Instancier les rôles constitutifs avec les ressources physiques : générateur
local du champ, état de la sonde, action de transport, horloge et autorisation
d'interaction. Le rôle de réception doit consommer une production antérieure
déterminée. Ses références ne deviennent pas des identifiants de coordonnées.

Schéma attendu, à préciser dans les types dépendants :

```text
step(prefix, instruction, ressources physiques reçues)
  -> production(action, mesure, support suivant, formation)
continuation(la même production.support suivant)
```

Les mises à jour de profil, d'action, de vecteur transporté et d'horloge seront
liées une seule fois. La connexion dérivée du champ reçu doit être utilisée
par l'action de transport. Une action indépendante accompagnée d'une preuve
de courbure inutilisée ne ferme pas ce lot. Cela vérifie une action sur
géométrie reçue ; le producteur intrinsèque R6 ne peut importer ce contrôle
pour prétendre avoir reconstruit cette géométrie.

Chaque parcours possède son curseur local et ses ressources de sonde ; les
lois et le champ partagé ne sont pas réécrits selon l'ordre d'ordonnancement
du programme. Un avancement local lit et poursuit sa réalisation du champ,
il ne modifie pas instantanément un champ global pour les autres parcours.
Le partage des données initiales et la séparation des ressources locales
doivent être positivement constitués, pas supposés par des copies anonymes.

Prouver : origine exacte des arguments, sortie de chaque producteur, transport
des anciennes occurrences, distinction des nouvelles, absence de queue future,
et partage des productions. À instruction et préfixe fixés, la tête ne dépend
pas d'un prolongement ultérieur. L'événement suivant est constitué depuis ces
sorties, non depuis une table géométrique préalablement écrite.

**Fermeture :** les données physiques gouvernent réellement les effets, tout
en restant indépendantes d'un choix arbitraire de coordonnées.

### B5. Poursuivre le générateur de référence et préserver ses contraintes

**Module :** `Comparison/ReferenceFieldExecution`, sur `PlaneWaveReference`.

Séparer trois opérations : poursuivre l'exécution, changer de coordonnées,
et produire une solution d'une équation d'évolution. Le résultat de l'une
ne sera pas annoncé comme une preuve des deux autres.

Pour les profils polynomiaux, construire l'avancement exact du générateur
depuis ses coefficients présents et un incrément reçu. Le décalage polynomial
donne les nouveaux coefficients sans lire les productions futures. Prouver
que la lecture après ce décalage est celle du même champ continu à l'endroit
suivant, et que la condition de vide est préservée.

Prouver par induction sur toute suite admissible de ces avances :

- chaque tête est produite avant sa continuation ;
- l'état suivant est celui de la production partagée ;
- domaine, orientation, raccords et contraintes physiques restent valides ;
- équations de champ et lectures sont les mêmes après changement de carte ;
- couper puis poursuivre un trajet donne l'action composée, sans réexécution.

Cette réalisation poursuit la lecture d'un champ dans la famille choisie.
Elle n'en démontre pas la génération par R6. Elle ne
résout pas un problème de Cauchy général : `u` est une coordonnée nulle,
pas une hypersurface spatiale ni un temps universel. L'interface générale
doit expliciter les données initiales, contraintes et domaine d'évolution
qu'elle demande ; toute revendication d'existence ou d'unicité plus large
exigera sa propre construction, non une hypothèse externe présentée comme fermée.

**Fermeture :** continuation effective et préservation prouvées pour toutes
les demandes admissibles du domaine réalisé, avec portée générique séparée.

### B6. Construire les chemins, les horloges et un effet de courbure observable

**Modules :** `Geometry/FrameTransport`, `Comparison/ReferenceFieldExecution`
et `Comparison/ReconstructedMeasurements` pour le raccord ultérieur à R6.

Le transport doit satisfaire l'équation différentielle de la connexion
construite, ses lois de composition et les retours lorsque l'inverse est
justifié. Un inverse géométrique ne fera pas remonter une production historique.
Ne pas imposer `AcceptanceAction.Coherent` à des chemins dont les effets
diffèrent : cette propriété doit être démontrée là où elle est vraie.

Ne pas supposer un solveur d'équations différentielles général pour fermer
cette première action. Sur les segments du premier scénario, paramétrés par
`u`, avec `B=0` et `y=0`, le calcul polynomial fournit un chemin explicite,
à dériver puis vérifier :

```text
deltaI   = primitive de A(u)*x(u), evaluee aux deux bornes
deltaH   = H lu a l'arrivee - H lu au depart
VuNext   = Vu
VxNext   = Vx - deltaI*Vu
VyNext   = Vy
VvNext   = Vv - deltaH*Vu/2 - deltaI*Vx + deltaI*deltaI*Vu/2
```

Prouver ces lois pour toute sonde source, pas seulement pour un vecteur choisi.
Les coefficients de segment viennent du générateur et des commandes présents,
les bornes de l'incrément admis ; aucune queue exécutée n'entre dans l'action.
Les mises à jour et les valeurs de `H` doivent être les sorties des producteurs
de B4-B5. Leur accord avec l'équation différentielle, la norme et la composition
est une preuve à construire, non une autorisation déduite du seul tableau.

Pour rendre la première fermeture précise, utiliser le profil `A(u)=1+u`,
`B=0` et deux trajets commandés sur `0 <= s <= 1` :

```text
u(s)       = s
xPlus(s)   =  r*s*(1-s)
xMinus(s)  = -r*s*(1-s)
y(s)       = 0
v'(s)      = (1 + x'(s)*x'(s) - H(s,x(s),0)) / 2
v(0)       = 0
```

Ils sont à produire depuis des instructions et ressources locales, puis à
interpréter par ces courbes. La formule n'autorise pas à prendre une trajectoire
complète comme entrée du producteur. Les commandes d'accélération sont des
entrées physiques déclarées ; ces trajets ne seront pas appelés géodésiques.

L'égalité de leurs coordonnées finales ne constitue pas le rendez-vous.
Instancier le rôle de rencontre de A1, section 7.3 : recevoir les références
distinctes des arrivées et de leurs sondes, construire l'autorisation locale
depuis ces productions, puis produire l'interaction commune. Conserver le
raccord du départ partagé, les deux histoires et les deux ressources d'arrivée.
La présence des instruments à la rencontre découle de ce raccord et des
lois de trajet ; elle n'est pas une identification des événements d'arrivée.

Prouver qu'ils sont futurs et temporels, qu'ils partent du même événement
et aboutissent à la rencontre constituée, avec des arrivées sources distinctes,
et que la norme de leur tangente est un. Leur temps propre entre ces événements
est donc un dans les unités fixées. Une sonde
vectorielle aura sa loi de transport déclarée et son couplage concret au
contrat ; ne pas confondre transport parallèle et loi d'un gyroscope accéléré.

Fermer aussi la commande de ces trajets accélérés : construire depuis le
curseur, la connexion et les commandes reçues l'action locale de contrôle,
puis prouver l'accord de son accélération covariante avec la tangente produite
et la conservation de sa norme. Une trajectoire symbolique temporelle n'est
pas à elle seule cette action. Les sondes restent celles du modèle test de
B3 ; aucune preuve de matière avec rétroaction ne découle de ces commandes.

Pour un vecteur initial dont la composante `u` vaut un et la composante `x`
zéro, l'équation de transport donne comme valeurs attendues `-r/4` et `r/4`
pour la composante transverse à la rencontre. Ces nombres doivent être
dérivés de la connexion et des actions exécutées, pas servir de sorties
prédéfinies. La mesure compare les deux sorties dans le même repère reçu
au même événement, par un produit métrique : ce n'est pas une différence
de composantes prises dans deux cartes indépendantes.

Pour les horloges, construire également le trajet de référence sur l'axe
`x=y=0` jusqu'à cette même rencontre : pour `0 <= s <= 1`, prendre
`u(s)=s` et `v(s)=vFinal*s`. Sa loi locale et sa calibration doivent être
réalisées comme celles des deux autres trajets ; sa durée ne se déduit pas
des seuls points d'arrivée. Les lectures attendues sont :

```text
vFinal       = 1/2 + 17*r*r/120
tempsAxe2    = 1 + 17*r*r/60
r            = 120/43
tempsAxe     = 77/43
tempsPlus    = tempsMinus = 1
```

La calibration positive de ces durées doit être construite. Une différence
d'horloge est un séparateur de trajets ; elle n'est pas, isolément, une preuve
de gravitation. La preuve de courbure et le séparateur vectoriel portent sur
la connexion de B2-B3. Le contrôle plat les distingue d'un simple effet de
choix d'horloge ou de coordonnées.

**Fermeture :** rendez-vous constitué, observations produites, effet de chemin
et durée propre raccordés aux lois, sans instrument supposé gratuitement.

### B7. Covariance des productions, des contrats et de la gravitation

**Module :** `ChartCovariance`, avec les lois de `DescriptionTransport`.

L'interface générale reçoit deux descriptions du même domaine, un changement
au moins quatre fois continûment différentiable, son inverse de même régularité
et leurs lois. Prouver les transformations de la métrique,
de la connexion, de la courbure, des tangentes, des sondes et des demandes.
La connexion ne sera pas transformée comme un simple tenseur : ses termes
de changement de coordonnées doivent être présents.

Fermer un premier changement de carte non affine :

```text
u' = u ; v' = v + c*x*x ; x' = x ; y' = y
inverse : v = v' - c*x'*x'
```

Son jacobien variable exige de traiter réellement les termes de transformation
de la connexion. Construire les retours et la régularité, puis prouver que
les productions et la poursuite donnent les mêmes observations transportées.
L'équation gravitationnelle et la distinction des trajets doivent rester
vraies dans cette seconde description.

Une équivalence de cartes ne change ni les événements déjà constitués, ni
le trajet physique de la sonde. Les lois génériques restent quantifiées sur
les changements satisfaisant leur interface ; le changement ci-dessus en
constitue un consommateur concret, pas la totalité des cartes possibles.

**Fermeture :** covariance de toute la chaîne, non seulement de l'intervalle.

### B8. Autoriser les regroupements par les futurs physiques

**Modules :** `Continuation/PhysicalContract`, `Grouping/DiscoveredRelations`,
`Grouping/FuturePreservation`, puis `Comparison/ReconstructedMeasurements`.

Raccorder au cas courbe le contrat intrinsèque fixé en A4, avant la réduction : commandes locales admissibles,
propagation et réception autorisées, lectures d'horloge, lectures des sondes
et comparaison au rendez-vous, avec refus explicites. Relier les lectures
aux instruments de B6. Construire au moins un échange de signal nul avec
émission et réception, puis fermer son admissibilité sur le domaine annoncé.
La seule existence abstraite d'un cône nul ne fournit pas cet échange.
Le cône de référence confirme les lois d'une action déjà admise ; il ne
fournit pas ses admissions amont. Un contrat spécialement défini sur le
fond reçu reste un contrôle comparatif et ne ferme pas le contrat de R1-R7.

Un premier signal fermé peut suivre la direction `E_v` : à `u,x,y` fixés,
produire un déplacement positif de `v`, puis la réception de sa sortie.
Prouver que sa tangente est non nulle, de norme métrique nulle et orientée
vers le futur selon B2, et que le rôle de réception consomme cette émission.
Cette voie est un cas physique du modèle, pas la totalité des propagations
lumineuses possibles.

Pour le scénario public, figer les commandes et paramètres permis, les
frontières locales où ils sont reçus et les lectures répétées après rencontre.
Une extension autorisant de nouvelles sondes ou interactions rouvre la preuve
d'exactitude ; elle n'est pas silencieusement incluse dans ce premier contrat.

La réalisation exacte porte sur toutes les listes finies de ce contrat,
leurs entrelacements, admissions et refus. L'exécution active garde la
production appariée ; la spécification ne réintroduit pas de doubles calculs.

Le même chercheur doit établir deux résultats depuis les contextes reçus :

1. Les présentations ne différant que par l'échange de productions indépendantes
   ont un raccord positif et peuvent être regroupées sous le contrat réalisé.
2. Les trajets dont les sondes ou horloges donnent des lectures différentes
   sont séparés par une demande de ce même contrat. Leur regroupement est refusé.

La complétude du chercheur ne portera que sur le domaine de transformations
construit. Un échec de recherche ne signifie pas qu'aucun autre transport
mathématique n'existe. L'autorisation doit être consommée par la réalisation
réduite ; une preuve de préservation seulement stockée à côté ne suffit pas.

Prouver les fibres exactes du régime produit, l'exactitude de tous les futurs
et les séparateurs. S'il est revendiqué minimal, prouver aussi la réciproque
comportementale et la nécessité des distinctions pour toute réalisation
exacte de ce même contrat. Sinon, annoncer seulement la réduction exacte,
sans importer la minimalité machine par analogie.

**Fermeture :** regroupement découvert, effets conservés et identités sources
distinctes ; une même rencontre géométrique ne suffit pas à autoriser l'oubli.

### B9. Certificat comparatif, quantifications et frontière de revendication

**Module :** `Comparison/ReferenceAgreement`, consommé ensuite par le
certificat final R7, mais insuffisant à le construire seul.

Le certificat doit épingler aux mêmes productions : rôles et événements,
champ et métrique réalisés, connexion et courbure calculées, équations,
continuations, observations physiques, relations trouvées, actions et mémoire.
Il épingle aussi les rencontres et leurs références sources, le domaine des
décisions d'admission, le pont des lectures exactes vers leurs interprétations
et le statut physique des instruments. Une équivalence de lectures n'est
pas un transport d'identité des événements.
Sa construction doit fermer les hypothèses de l'instance sans certificat
étranger ou trajectoire terminée fournie indépendamment. La métrique de
référence est explicitement déclarée. Son existence ne tient pas lieu de
la métrique reconstruite ; leur accord doit être un résultat de R5-R7.

Les consommateurs publics doivent appliquer directement les résultats sur
les objets réalisés. Ils démontreront le cas courbe, le contrôle plat, les
deux descriptions et les regroupements autorisés/interdits, sans adaptateur
de carrier qui rompe une détermination constituée.

| Niveau | Quantification à annoncer | Condition de fermeture |
| --- | --- | --- |
| Interfaces géométriques et physiques | Tout objet satisfaisant les hypothèses régulières déclarées | Lois génériques prouvées ; pas de prétention d'existence automatique |
| Famille géométrique d'ondes | Tous les profils polynomiaux du domaine analytique construit | Régularité, signature, courbure et vide fermés |
| Générateur d'ondes exécutable | Tous les coefficients rationnels exacts admis et leurs domaines réels interprétés | Production, avancement, admission et raccord analytique fermés |
| Instruments du premier scénario | Toutes les commandes de sondes tests admises sur ce fond | Actions, calibrations et mesures fermées ; rétroaction non incluse |
| Exécution publique | Tous les préfixes et toutes les demandes autorisées du scénario | Formation, partage, continuation et effets exacts |
| Contrat de mémoire | Toutes les listes finies du contrat fixé | Réalisation exacte ; nécessité/minimalité seulement si leurs preuves sont présentes |
| Reconstruction constitutive | Classe fixée en A0, productions et continuations de R1-R6 | R7 fermé, avec couverture et réciproques ; B0-B9 seuls ne suffisent pas |

La loi d'Einstein et les primitives physiques sont déclarées comme lois du
modèle, puis satisfaites par la construction. Les dériver des seules quatre
fondations serait une autre obligation, qui ne sera ni prétendue accomplie
ni substituée à la cible actuelle. Aucune universalité sur tous les espaces-
temps, aucune résolution générale des équations et aucune validation
expérimentale ne découle de ce certificat par changement de vocabulaire.

La clôture finale exige A0-A4 et R1-R7, pas seulement cette comparaison.
Un obstacle sur la genèse, la continuité, le raccord analytique, la mesure
ou l'autorisation demeure un obstacle à cette clôture, même si la métrique
de référence satisfait les équations de vide.

## 14. Ordre d'implémentation et gates de décision

| Gate | Doit être fermé avant de poursuivre | Échec interdisant la revendication |
| --- | --- | --- |
| G0 / A0 | Lois intrinsèques candidates, classe non triviale et contrat fixés ; premier raccord identifié | Géométrie fournie sous un nom relationnel, classe définie par la conclusion |
| G1 / A1 | Rôles, ressources, événements et rencontres positivement constitués ; origine du préfixe et curseur complet raccordés | Valeur libre avec provenance adjacente, rencontre depuis des coordonnées, simple égalité d'endpoint remplaçant l'origine produite |
| G2 / A2 | Dépendances utilisées et influences admissibles séparées | Chronologie de liste ou cône reçu substitués aux influences |
| G3 / A3 | Échanges indépendants avec retours et provenance | Égalité finale seule, occurrences identifiées |
| G4 / A4 | Admissions locales, refus et toutes suites du contrat | Appel à la métrique aval, restriction postérieure aux résultats |
| G5 / R1 | Recherche exécutée, action, autorisation et organisation suivante consommées | Singleton indépendant, production prescrite, témoin supprimable sans effet sur l'autorisation |
| G6 / R1 | Tête complète sans futur, continuation sur les sorties partagées, reprises de longueur arbitraire depuis le curseur atteint | Objet tête enrichi par la queue, producteur ancien réexécuté ou plafond global substitué à l'horizon arbitraire |
| G7 / R2 | Accord conjoint, chaînes de projections, jonctions autorisées et transports de description distincts ; effets et contrats préservés | Une chaîne de noyaux substituée à l'accord de tous les lecteurs ; différence physique effacée |
| G8 / R3 | Présentations riches, localisation d'espace-temps et effets attachés ; accords, extension et raffinement distincts avec leurs lois de raccord ; traces et autorisations transportées sous le même contrat | Point reçu, provenance adjacente, position spatiale confondue avec événement, effet de parcours effacé, mesure confondue avec description, nouvelle présentation détachée de la détermination ancienne |
| G9 / R4 | Règles de recouvrement justifiées, réalisations cohérentes, accords, points et voisinages, actions continues et couverture | Recoupement traité comme équivalence, raffinement d'une seule occurrence, choix implicite de réalisations, simple limite de partitions ou domaine fourni |
| G10 / R5 | Dimension, cartes, retours et régularité justifiés | Quatre labels présentés comme une variété de dimension quatre |
| G11 / R5 | Causalité et métrique calibrée raccordées aux effets | Facteur d'échelle non fixé, signature fournie annoncée comme dérivée |
| G12 / R6 | Action de chemin, connexion et courbure sur la même construction | Connexion indépendante ou cohérence qui annule un effet physique |
| G13 / R6 | Champs poursuivis, contraintes et lois dynamiques réalisées | Lecture d'une solution reçue confondue avec sa production, matière définie comme résidu |
| G14 / R7 | Comparaison complète, couverture, réciproques et hypothèses globales | Plongée seule, carte locale déclarée domaine entier |
| G15 / R7 | Classe réalisée, certificat fermé et consommateurs publics | Interface sans instance, ancien maître affaibli, certificat comparatif déclaré genèse |

**Ordre effectif :** commencer par G0, A1-A4 puis R1-R3. Fermer un premier
consommateur intrinsèque et ses séparateurs avant d'étendre l'analyse.
Développer les outils de B0 nécessaires à R4-R6, puis fermer R4-R7 dans
l'ordre de leurs dépendances : règles de recouvrement avant les présentations
idéales, celles-ci avant les cartes et la métrique. Les contrôles A5-A8 et
B1-B9 accompagnent les raccords déjà construits ; ils ne peuvent franchir
une gate R manquante.

Les certificats intermédiaires annonceront exactement leurs gates fermées.
Une réussite plate, une courbure calculée ou un raccord à une métrique reçue
ne valideront pas G8-G15. Une gate est réouverte si une loi, un contrat,
une présentation ou un consommateur dont elle dépend change.

**Premier livrable d'implémentation après autorisation :** une définition
concrète des primitives candidates de A0, une exécution locale de A1-A4,
une organisation regroupante et un séparateur de R1-R2, puis le premier
raccord de présentation/raffinement de R3 : constructeurs fermés, transport
de description et raffinement commun, distincts d'une nouvelle mesure.
Inclure une variation non triviale des interactions et lectures admises,
et la première règle de recouvrement justifiée par leurs lois. Conserver
un témoin de rencontre commune avec des effets de parcours encore séparables.
Inclure une reprise depuis un premier suffixe effectivement produit et les
lois génériques de composition, de conservation des références et de raccord
avec le raffinement. Les longueurs sont arbitraires ; les deux suffixes du
consommateur concret illustrent ces lois et ne remplacent pas leur preuve.
Ce livrable ne ferme pas le continuum ; il doit décider si le premier
passage annoncé est réellement disponible. Il ne sera pas remplacé par
un nouveau backend numérique ou un calcul de référence plus détaillé.

## 15. Vérification proportionnée et non-régression

La démonstration guide l'implémentation. Les contrôles servent ensuite à
vérifier qu'elle est présente dans les sources et leurs consommateurs.

Pour chaque lot : compiler les modules et un client de la surface publique,
contrôler les audits axiomatiques, la calculabilité et les hypothèses exactes.
Vérifier les témoins positifs ainsi que les cas qui doivent rester distincts.
Ne pas employer d'axiome d'extensionnalité pour fermer une égalité.

Pour les points critiques, quelques substitutions cohérentes auront une
obligation de rejet précise : sortie prescrite, lecture de queue future,
capture non déclarée, ordre global utilisé comme causalité, regroupement des
horloges distinguées, transport qui altère un invariant. Une erreur de nom
ou de lint ne sera pas une preuve de rejet scientifique. Une substitution
extensionnellement équivalente n'est pas un échec si tous les raccords
constitutifs et tous les effets autorisés restent effectivement préservés.

Les raccords critiques ont des consommateurs
obligatoires, à construire pendant l'implémentation :

| Raccord | Consommateur positif | Interdiction à vérifier |
| --- | --- | --- |
| Lectures exactes et analyse | Injection rationnelle fidèle et accord de deux représentations de la même valeur | Déduire une égalité d'occurrences ou d'encodages depuis cet accord |
| Admission exécutable | Avance admissible et ses bornes, puis refus d'une avance nulle ou hors domaine | Se donner une comparaison totale de réels pour fermer le contrat |
| Rencontre | Arrivées réellement reçues, références distinctes et interaction produite | Fabriquer la rencontre depuis la seule égalité de coordonnées |
| Instruments tests | Action de contrôle, transport et calibration utilisés par les mesures | Présenter le fond de vide comme une réalisation de leur rétroaction |
| Organisation et présentations | Constructeurs consommant les productions, attachements et raccords autorisés | Carrier libre ou géométrie indépendante avec une trace ajoutée à côté |
| Projections complémentaires | Accord conjoint séparé des chaînes ; action autorisée et futur séparateur de parcours | Effacer globalement une différence que seule une projection ignore |
| Localisation et effets attachés | Accord de localisation à une rencontre, effets de parcours encore distinguables | Faire de chaque état d'appareil un lieu distinct ou oublier ses effets parce que les lieux s'accordent |
| Extension et raffinement | Nouvelle mesure exécutée puis transport de la détermination ancienne ; restrictions de précision | Lire une queue future ou recréer rétroactivement l'événement décrit |
| Préfixe et reprises | Origine produite, curseur complet, deux suffixes partagés ; composition des références et transport des regroupements | Choisir une autre origine au même endpoint, rejouer l'ancien producteur, borner globalement les futurs |
| Raffinement et continuité | Famille réalisable, contraintes ouvertes, limites et couverture construites | Confondre configuration d'instruments, chaîne de regroupements, grille et continuum physique |
| Structure reconstruite et relativité | Cartes, calibration, connexion et loi dynamique avec comparaison dans les deux sens | Supposer les structures dans le contrat amont, se contenter d'une plongée |

Ne pas imposer aux étapes physiques la décroissance de rang des règles de
normalisation : cette mesure justifie un algorithme de regroupement, pas la
totalité des continuations du modèle physique.

Avant livraison exécutable :

```text
python3 scripts/check-scientific-docs.py --self-test
python3 scripts/check-scientific-docs.py --static
lake build +RelationalPerimeter
lake build
python3 scripts/check-scientific-docs.py --lean
bash scripts/verify.sh
pwsh -NoProfile -File scripts/verify.ps1
git diff --check
```

Ces commandes désignent les contrôles à lancer lors de l'implémentation,
pas des résultats déjà obtenus pour des modules inexistants. Les deux
vérificateurs devront couvrir les nouvelles sources et conserver leurs
gates actuelles. Documenter les plateformes effectivement testées.

Comparer les quatre fondations, la cible canonique, les déclarations publiques
existantes et les scénarios maître/SAT/mémoire au snapshot initial. Aucun
résultat antérieur ne sera supprimé pour faciliter ce lot. Les nouvelles
strates ne devront pas créer d'orphelin ni d'import ascendant.

## 16. Documentation et futur audit scientifique

Après les preuves, écrire un texte FR/EN distinguant : données déclarées,
productions, réalisations, transports, effets observables et hypothèses
physiques. La notation `e |= P` pourra montrer plusieurs garanties du même
objet, mais ne remplacera ni ses indices dépendants ni ses témoins.

Enregistrer chaque nouvelle affirmation dans le registre avec ses sources,
sa portée et ses consommateurs. Ne pas actualiser les empreintes anciennes
pour dissimuler une modification. Une nouvelle évidence documentaire requiert
sa révision propre et les autorisations de commit appropriées.

L'audit du premier lot devra examiner les gates effectivement fermées de
G0-G8, sans les transformer en validation de R4-R7. L'audit de la cible
finale doit examiner G0-G15 : genèse, reconstruction, continuité, géométrie
et dynamique, avec couverture et réciproques. Une matrice de Lorentz,
une table d'horloges ou B0-B9 seuls ne suffisent pas. Les
conclusions et les limites seront citées exactement ; ni le verdict historique
ni l'acceptation d'une soumission ne
serviront de validation de cette extension.

Pas de nouveau diagramme scientifique, publication, commit, push ou audit
extérieur sans demande. Aucun matériel particulier n'est requis pour le
lot mathématique plat. Un raccord expérimental à des horloges et signaux
réels demanderait un protocole physique distinct, pas seulement un build Lean.

## 17. Faisabilité, décision suivante et limite exacte de cette révision

La version précédente préparait un raccord de productions à une géométrie
reçue. Elle ne préparait pas suffisamment sa genèse. Cette révision change
l'ordre et les critères du plan pour respecter l'objectif précisé, sans
modifier les résultats acquis ni prétendre que les nouveaux lots sont fermés.

Le point ouvert principal n'est pas seulement une difficulté de backend :
**les primitives physiques non géométriques et le mécanisme effectif qui
conduit de leurs regroupements à un domaine continu doivent encore être
construits.** Les fondations génériques et la machine donnent des interfaces
et des preuves de méthode ; elles ne sélectionnent pas seules les lois de
la physique ni ne démontrent déjà une variété lorentzienne.

Le chemin de la section 4.1 ferme déjà dans le maître l'origine produite,
la tête sans futur, le prolongement de longueur arbitraire et le transport
historique des regroupements. Ce sont des constructions existantes, pas
des solutions à chercher dans une autre fondation. Leur spécialisation
physique et son contrat doivent encore être réalisés.

R2-R4 poursuivent ce chemin : présentations finies formées sur ces mêmes
productions ; accords et restrictions ; contraintes et recouvrements
justifiés ; localisations cohérentes et effets attachés conservés ; actions
continues et couverture. Les lois de cette organisation aval restent à
démontrer depuis les raccords internes, sans topologie fournie en amont.
Ces lots ne sont pas encore réalisés. En particulier, aucune primitive
physique candidate n'est ici construite, aucun système physique de
recouvrements n'est réalisé et aucune couverture relativiste n'est prouvée.

Pour démarrer, A0 doit examiner une loi locale candidate dans ses données
et ses termes, puis construire ses producteurs, effets, lecteurs et séparateurs.
Les échecs doivent localiser une obligation : propriété géométrique déjà
encodée dans la primitive, contrat trop pauvre, absence de raffinement
compatible, réalisations non cohérentes, prolongement ou transport détaché
de la détermination constituée, défaut de points ou de couverture, ou
distinction physique perdue. Ajouter
un témoin libre à une structure ne résout aucun de ces cas.

La continuité R4, les cartes et la calibration R5, puis le raccord dynamique
R6 sont des obligations de recherche, pas des conséquences automatiques
du regroupement. Leur faisabilité constructive reste à démontrer. Le plan
n'annonce donc ni impossibilité acquise ni réussite garantie. Si une
obligation échoue, l'état sera « cible non établie » avec le lemme manquant ;
pas « cible atteinte » au prix d'un objectif voisin.

Les exemples plats et courbes conservés ont fait l'objet, lors de la version
précédente, de contrôles algébriques rationnels : inverses, Ricci nul,
courbure non nulle, normes des tangentes, transport transverse et durée
`77/43` pour le témoin indiqué. Ce sont des contrôles de cohérence des
références, pas des preuves Lean de genèse, ni des expériences physiques,
ni une validation indépendante. Ils n'ont pas été rejoués pour cette
révision purement documentaire.

La relecture actuelle vérifie l'ordre des dépendances, les consommateurs,
les accords et recouvrements, la distinction entre occurrence et localisation,
la séparation entre extension et raffinement, les effets attachés, la portée
et les critères de clôture. Aucun fichier Lean, contrat existant,
fondation ou cible computationnelle canonique n'est modifié par cette
révision. L'état numérique effectivement implémenté suit ci-dessous.

## 18. État réel de l'implémentation : prérequis de B0

Les constructions suivantes existent dans les sources, avec leurs preuves
constructives et leurs audits axiomatiques finaux :

| Construction | Sources | Portée exacte |
| --- | --- | --- |
| Lois arithmétiques élémentaires | `Arithmetic/NaturalLaws.lean`, `Arithmetic/SignedBalance.lean` | Preuves par induction et élimination d'égalité ; encodages signés non identifiés |
| Fractions et couverture de leur énumération | `Arithmetic/FractionRepresentation.lean`, `Arithmetic/PairEnumeration.lean` | Lois de représentation et recherche finie réellement couverte |
| Rationnels canoniques | `ExactArithmetic.lean` | Égalité numérique reflétant l'accord par produits croisés, opérations exécutables et lois de l'anneau |
| Comparaisons et bornes | `Arithmetic/OrderedFractions.lean` | Décisions sur rationnels exacts, produit de valeurs non négatives et bornes construites |
| Représentations de Cauchy | `Analysis/ConstructiveContinuum.lean` | Moduli explicites, témoins positifs d'accord ; addition, négation, multiplication et compatibilité de l'accord |
| Injection rationnelle fidèle | `Analysis/ReadoutInterpretation.lean` | L'accord des lectures constantes reflète leur égalité rationnelle ; deux encodages effectivement différents peuvent être analytiquement en accord |
| Calcul polynomial partagé | `Analysis/PolynomialCalculus.lean` | Évaluation, jets, dérivation formelle et primitive formelle avec lois exactes |
| Interprétation polynomiale | `Analysis/PolynomialInterpretation.lean` | Évaluation sur les représentations analytiques, préservation de l'accord des coordonnées et raccord aux évaluations rationnelles |

Ces fichiers sont sous `RelationalPerimeter/Relativity/`. La façade
`RelationalPerimeter/Relativity.lean` ne présente pas de certificat physique.
`Tests/Relativity/NumericalChecks.lean` les consomme depuis l'unique racine
publique. Les fichiers existants du maître et de la machine ne sont pas
modifiés.

La normalisation rationnelle utilise une énumération finie dont la couverture
et le représentant minimal sont prouvés. Ce premier backend privilégie la
correction constructive, pas l'efficacité. Aucune borne de coût polynomial
ni aptitude de ce backend à une simulation physique de grande taille n'est
revendiquée. Son éventuel remplacement devra conserver les mêmes lois.

La multiplication analytique ne reçoit pas une borne de séquence laissée
ouverte. `tailBound` la construit depuis une approximation effective au seuil
du modulus de précision un ; `productPrecision` calcule les précisions
requises, puis `mul` et `mulAgreement` consomment ces bornes pour construire
leurs témoins. L'accord est un objet avec modulus, pas une extraction depuis
une existence effacée ; il n'implique pas l'égalité des encodages.

**B0 demeure ouvert.** Les lois de dérivation et de primitive actuellement
prouvées sont algébriques. Il manque leur interprétation par limites sur le
domaine analytique, les régularités C3/C4 requises, les lois d'ordre et les
constructions analytiques encore nécessaires (notamment complétude et
inverse avec apartness lorsque la réalisation les utilise), ainsi que les
opérations matricielles raccordées à ce domaine. L'évaluation polynomiale
sur des représentations de Cauchy ne ferme aucune de ces obligations à elle
seule.

Le premier candidat local de production est décrit en section 20. Les lots
physiques complets, de rencontres, d'horloges, de changements de description,
de connexion, de courbure, de dynamique gravitationnelle et de regroupement
sous contrat ne sont pas déclarés fermés. Aucun résultat symbolique ou
numérique n'est substitué à la cible de la section 1.

## 19. Vérifications antérieures exécutées sur le sous-lot numérique

État local non commité de la branche `relativite`, au-dessus de la révision
de départ indiquée en section 2. Ces vérifications ne sont pas un audit
indépendant et ne ferment pas les lots physiques. Elles sont conservées
comme compte rendu du sous-lot précédent ; aucun build n'a été relancé pour
cette révision du Markdown, qui ne modifie pas les sources compilées.

- Compilation individuelle des nouveaux modules et consommation des
  principales déclarations depuis `Tests/Relativity/NumericalChecks.lean`.
- `lake build` : réussite, 258 jobs, aucun avertissement Lean.
- Audit exhaustif : 21 211 constantes, 255 modules importés, aucune exception
  écrite à la main. Les 364 exceptions sont les déclarations générées déjà
  classifiées par le contrôleur du dépôt.
- `scripts/verify.ps1` et `bash scripts/verify.sh`, exécutés tous deux sous
  Windows : réussite sur les mêmes 256 fichiers Lean, avec les contrôles
  d'imports, de stratification, de références documentaires, de code compilé
  et les 23 fixtures devant échouer.
- Les deux contrôleurs de stratification : 211 modules de production,
  tous contraints et accessibles depuis les racines publiques, aucun orphelin.
- Scan des constructions interdites : aucun résultat ; un seul bloc d'audit
  placé à la fin de chacun des 256 fichiers Lean.
- `git diff --check` : réussite. Git signale uniquement sa politique de
  conversion LF/CRLF du manifeste de stratification, pas un défaut du diff.
- Les quatre fondations, le maître, la machine, les contrats existants,
  le registre scientifique, la toolchain, la configuration Lake et son
  manifeste sont inchangés. La racine publique reçoit seulement l'import
  de la façade numérique ; l'audit exhaustif reçoit le nouveau client de test.

Le `#eval` de l'addition de deux demis est un smoke test d'exécutabilité,
pas une expérience confirmatoire ni une mesure de coût. Le C produit pour
`evaluateJet` a été lu : les branches somme et produit appellent chacune
une fois l'évaluateur sur chaque enfant et réutilisent ses deux sorties.
Cette lecture locale ne prouve pas un coût total minimal et n'est pas une
gate de partage pour la future machine physique.

Les statuts ouverts du registre existant restent ouverts. Aucune empreinte
scientifique ancienne n'a été actualisée et aucun résultat nouveau n'a été
présenté comme audité. Aucun commit, push ou audit extérieur n'a été réalisé.

## 20. Premier sous-lot de production locale

La première loi candidate est déclarée, et non déduite de la relativité :
émission d'un enregistrement depuis une lecture d'instrument et un contenu
reçus ; propagation ajoutant un incrément rationnel calibré positif ;
réception produisant la lecture de l'enregistrement effectivement reçu.
L'enregistrement conserve la liste de ses incréments. Sa lecture n'est
déclarée ni temps propre, ni temps global, ni distance. Aucune coordonnée,
métrique, variété ou vitesse de propagation ne figure dans les entrées.

Les fichiers actuels sont :

- [PhysicalPrimitives](../../RelationalPerimeter/Relativity/Production/PhysicalPrimitives.lean) :
  données reçues et loi locale ; calibration unité positivement construite.
- [LocalInstructions](../../RelationalPerimeter/Relativity/Production/LocalInstructions.lean) :
  grammaire fermée de ports typés et relation positive `Produces`.
  La sortie est formée avec son témoin, pas prescrite puis annotée.
- [OccurrenceTransport](../../RelationalPerimeter/Relativity/Production/OccurrenceTransport.lean) :
  transport ancien/frais avec les deux retours ; les hypothèses du rôle
  résiduel sont fermées sur ces occurrences, pas laissées externes.
- [ConstitutedEvents](../../RelationalPerimeter/Relativity/Production/ConstitutedEvents.lean) :
  histoire de formation constituée depuis les ressources reçues ; projection
  incrémentale sur le support générique avec le même rôle ; paire de production
  partagée ; continuation sur le curseur complet réellement produit.
  `ResourceInterpretation` impose dans le type du curseur le raccord de la
  racine et de chaque rôle : la formation générique ne peut être seulement
  un témoin adjacent portant les mêmes valeurs finales.
- [CalibratedRelay](../../RelationalPerimeter/Relativity/Production/CalibratedRelay.lean) :
  famille paramétrée par les données reçues et une longueur finie arbitraire.
- [LocalProductionChecks](../../Tests/Relativity/LocalProductionChecks.lean) :
  consommateurs publics, sorties incorrectes réfutées, retour des transports,
  conservation des lectures, distinction de ressources aux valeurs égales
  et smoke test d'exécutabilité.

La grammaire du programme indexe seulement les sortes de ressources qui
deviendront disponibles. Elle ne contient aucun curseur futur déjà calculé.
Le runner évalue la tête, lie sa sortie et son successeur, puis transmet ce
successeur à la suite. L'histoire fondée de `StrongPerimetralTurning` stocke
la détermination obtenue. Les ports anciens sont injectivement conservés
avec leurs lectures, pour toute histoire locale construite.

Le nombre de relays décrit ce programme fini. Le théorème de longueur vaut
pour tout nombre naturel ; ce nombre n'est pas une durée physique. Les
témoins et les histoires restent présents dans ce prototype : aucune borne
de mémoire, minimalité, réduction de cache ou réalisation matérielle n'est
revendiquée. La lecture du C généré vérifie localement un appel à `execute`
dans `perform`, puis un appel à `perform` avant la récursion dans `runFrom`.
Elle n'est pas une certification de coût total.

**Portée non fermée :** ce sous-lot ne clôt pas tout A0 ni A1-A4. Le contrat
physique des futurs, les rencontres, l'échange des productions indépendantes,
la recherche de regroupements, leurs séparateurs et les raffinements restent
à construire. En particulier, cette loi locale n'est pas encore démontrée
suffisante pour produire les recouvrements de R4 ou un domaine relativiste.
Le regroupement et la reconstruction intrinsèque R1-R7 restent des
obligations, pas des conséquences annoncées de ce premier candidat.

Les strates locales `H0` à `H4` sont séparées des utilitaires numériques `T`.
Elles ne peuvent importer ni le maître computationnel ni la machine. Les
fondations, la cible et les contrats existants sont conservés. La réussite
des contrôles locaux n'est pas un verdict d'audit indépendant.

### Contrôles exécutés sur ce sous-lot

- `lake build` : réussite, 264 jobs, aucun avertissement Lean.
- Audit exhaustif : 21 584 constantes, 261 modules importés, aucune
  dépendance axiomatique écrite à la main ; 364 exceptions générées,
  classifiées par le contrôleur existant, sans modification de ses règles.
- `bash scripts/verify.sh` et `pwsh -NoProfile -File scripts/verify.ps1`,
  tous deux sous Windows : réussite sur les mêmes 262 fichiers Lean et
  les 23 fixtures devant échouer pour leurs diagnostics et sites exacts.
- Stratification : 216 modules de production, tous contraints et
  accessibles depuis les racines publiques ; aucun orphelin.
- Contrôles documentaires, références Lean publiques et de tests, frontières
  d'import et contrôles du code compilé existant : réussite.
- Comparaison SHA-256 avec l'état avant ce sous-lot : aucune suppression ;
  les quatre fondations, le maître, la machine, les utilitaires numériques,
  la cible canonique, le registre et la configuration restent inchangés.
- `git diff --check` : réussite ; seul avertissement Git de conversion
  LF/CRLF du manifeste de stratification.

Un lancement simultané des deux vérificateurs a rencontré une erreur de
fichier dans le build PowerShell. Le vérificateur Bash a terminé avec succès ;
le vérificateur PowerShell, relancé seul ensuite, a terminé avec succès.
Cette tentative en échec n'est pas comptée comme une validation.

Le `#eval relaySmoke 3` est un smoke test uniquement. Aucun protocole
confirmatoire, mesure physique, audit indépendant, commit ou push n'a été
réalisé. Les revues ouvertes du registre restent ouvertes.

## 21. Continuations locales, admissions et dépendances utilisées

La demande « tu peux poursuivre l implementaiton » autorise ce sous-lot
sur la même branche isolée. La cible de la section 1, les fondations, le
maître et ses contrats restent inchangés. Les sections 19 et 20 décrivent
leurs vérifications historiques, non celles de ce nouveau sous-lot.

### Contrat fixé pour le candidat actuel

Le contrat est défini avant tout regroupement ou oubli. Il autorise des
listes finies de longueur arbitraire des demandes suivantes, dans tous
leurs entrelacements :

| Demande | Admission construite | Production et événement |
| --- | --- | --- |
| Émettre | Référence disponible de lecture et référence de contenu | Signal constitué depuis ces deux ressources, avec liste d'incréments vide |
| Propager | Référence disponible de signal et référence de calibration | Signal constitué depuis le signal reçu et l'incrément calibré ; parcours enregistré |
| Recevoir | Référence disponible de signal | Nouvelle lecture constituée depuis ce signal |
| Inspecter | Référence disponible de la sorte demandée | Lecture de la ressource existante ; aucune nouvelle production |
| Demande hors domaine | Réfutation de la référence typée requise | Refus explicite ; curseur conservé |

Les adresses naturelles sélectionnent des ressources dans le contexte
actuel. Elles ne sont ni coordonnées spatiales, ni dates, ni distances.
L'admission est effectivement résolue depuis ce contexte : un témoin
positif fournit les ports, sinon la référence demandée est réfutée.
La calibration porte déjà la loi positive du candidat.

L'inspection d'un signal expose son contenu, sa lecture rationnelle et
toute la liste de ses incréments. L'inspection d'une calibration expose
son incrément. Il n'y a pas d'observation passive supplémentaire : le
champ `read` du contrat vaut `Unit`. Les histoires de formation ne sont
pas directement inspectables ; leurs effets accessibles le restent par
les demandes du contrat. Ce contrat local n'est pas déclaré égal au
contrat physique final de A4 : rencontres, correspondances entre ordres
et raffinements devront y être intégrés avec leurs preuves propres.

### Passages réalisés

| Passage | Source | Ce qui est effectivement construit |
| --- | --- | --- |
| Ports lus et dépendances | [UsedDependencies](../../RelationalPerimeter/Relativity/Production/UsedDependencies.lean) | Arêtes positives indexées par la formation et par les ports du rôle exécuté ; chemins non vides composables et transportés dans l'histoire suivante |
| Admission et refus | [PortAdmissions](../../RelationalPerimeter/Relativity/Production/PortAdmissions.lean) | Résolution exécutable de la référence avec son adresse exacte, ou réfutation ; extraction positive du témoin admis |
| Futurs et lecteurs fixés | [LocalFutureContract](../../RelationalPerimeter/Relativity/Production/LocalFutureContract.lean) | Contrat total ; exactitude de l'inspection de toute référence disponible ; nécessité de l'accord de ses readouts sous équivalence future |
| Exécution et continuation | [RequestedExecution](../../RelationalPerimeter/Relativity/Production/RequestedExecution.lean) | Une paire événement/successeur issue de la même production ; histoire construite avec cette détermination ; suite exécutée depuis le curseur produit |
| Consommation publique | [LocalContinuationChecks](../../Tests/Relativity/LocalContinuationChecks.lean) | Admission et refus, transport d'arêtes, entrelacements, continuation et séparateur de parcours, depuis `import RelationalPerimeter` |

Les arêtes utilisées ne sont pas déduites d'un ordre de positions : leur
construction consomme le port de la production dans son histoire de
formation. La diminution des positions vient ensuite et prouve l'absence
de cycles dans ce modèle incrémental. Le transport d'une arête consomme
le raccord exact du successeur et la transmet sur les références conservées.
Les fonctions `transportUsed` et `transportPath` reçoivent le résultat déjà
exécuté ; elles ne relancent pas ses demandes pour reconstruire son histoire.
Cette acyclicité ne prétend pas exclure toutes les courbes causales fermées
d'une théorie relativiste.

`PermittedUse` est distinct de `Used`. Le premier est un témoin qu'une
instruction locale pourrait lire un port disponible ; il ne constitue
pas une émission, une dépendance déjà exécutée, ni la relation physique
d'influence admissible encore à construire en A2.

`requests_all_futures_exact` quantifie sur tout curseur constitué et toute
liste finie de demandes du contrat, sans plafond de longueur et en incluant
les refus. La preuve procède par induction sur cette liste ; elle raccorde
à chaque étape l'admission, l'événement et le successeur réels à leur
spécification. `requests_final_cursor_exact` raccorde également le curseur
final. `continue` exécute seulement la suite depuis le curseur déjà produit.
`continuedHistory` reçoit cette suite déjà exécutée : il assemble les deux
histoires conservées sans appeler le producteur ni relancer les demandes.
Le rapport retourné par `continue` décrit la suite, pas une nouvelle
exécution du préfixe.

La spécification `FutureContract.outcome` utilise séparément ses projections
de successeur et d'événement. Elle n'est pas le runner à production partagée.
Les affirmations d'exécution unique concernent `performRequest`, `runRequests`
et la reprise depuis un résultat conservé, pas l'évaluation de cette
spécification générique ni des appels répétés du consommateur au runner.

### Distinction de parcours effectivement révélée

Un premier parcours émet un signal puis lui applique deux incréments unité.
Une continuation reçoit sa lecture et réémet depuis cette lecture produite.
Les signaux finaux ont la même lecture rationnelle, mais leurs listes
d'incréments ont respectivement deux éléments et aucun. L'inspection admise
du signal révèle cette différence.

`path_record_is_future_separable` réfute donc leur équivalence future sous
le contrat fixé. Il utilise le théorème général
`futures_preserve_available_readout`, pas une simple comparaison informelle
des traces. Ce théorème impose l'accord des readouts de ressources de même
sorte accessibles à une même adresse si les futurs sont équivalents ; il
n'identifie pas leurs occurrences sources. La nécessité obtenue concerne
ce contrat précis et ne prétend pas caractériser toute mémoire physique.

### Frontière inchangée de la cible

Les données initiales et la loi calibrée sont reçues ou déclarées ; les
admissions, productions, chemins utilisés et reprises sont construits.
Aucune recherche de regroupements, rencontre physique, influence
relativiste, réduction mémoire, géométrie, dynamique gravitationnelle ou
reconstruction du domaine n'est déclarée prouvée par ce sous-lot. Les
témoins et les histoires restent stockés. Aucune borne de coût, minimalité
physique ou mesure confirmatoire n'est annoncée.

Les nouveaux modules sont contraints dans les strates `H3` à `H5` ; la
façade est désormais en `H6`. Les imports de la production locale ne
peuvent remonter vers le maître ou la machine ; les utilitaires numériques
restent séparés. Les obligations complètes de A0-A4 et R1-R7 restent celles
du plan, sans substitution par le seul contrat local construit ici.

### Vérifications exécutées sur l'état final du sous-lot

- Compilation du nouveau client public : réussite, audits de ses nouvelles
  déclarations sans axiome ; smoke tests donnant les deux longueurs de
  parcours attendues. Ces évaluations ne sont ni une mesure de coût ni une
  expérience physique.
- `lake build +RelationalPerimeter` : réussite ; les deux vérificateurs
  reconstruisent ensuite le paquet complet après les derniers changements.
- `bash scripts/verify.sh`, puis `pwsh -NoProfile -File scripts/verify.ps1`,
  exécutés séquentiellement sous Windows : réussite sur les mêmes 267
  fichiers Lean, avec les 23 fixtures attendues et leurs diagnostics exacts.
- Build complet final : 269 jobs, aucun avertissement Lean. Audit exhaustif
  de 21 952 constantes dans 266 modules importés : aucune dépendance
  axiomatique écrite à la main ; 364 exceptions générées classifiées par
  les règles existantes inchangées.
- Stratification : 220 modules de production, tous contraints et accessibles
  depuis les racines publiques ; aucun orphelin.
- Un unique bloc d'audit final dans chacun des 267 fichiers Lean ; aucun
  résultat au scan des constructions interdites.
- Contrôles du registre, des liens, des références Lean, des frontières
  d'import et du code compilé existant : réussite. Les revues ouvertes du
  registre restent ouvertes ; aucune empreinte scientifique actualisée.
- Lecture locale du C généré de `RequestedExecution` : un appel au producteur
  dans chaque branche d'action admise, aucun dans l'inspection ou le refus ;
  une réponse partagée avant l'appel récursif de la suite. `continuedHistory`,
  `transportUsed` et `transportPath` consomment les histoires conservées sans
  appeler le runner. Cette lecture n'est pas une gate automatique générale
  ni une preuve de coût physique total.
- Comparaison SHA-256 avec le début du sous-lot : aucune suppression et aucun
  changement des fondations, du maître, de la machine, des utilitaires
  numériques, des contrats antérieurs, de la cible canonique, du registre
  ou de la configuration Lean. Seuls les nouveaux modules, leur façade,
  leur import d'audit, leurs contrôles de stratification et ce plan évoluent.
- `git diff --check` : réussite ; Git signale seulement la conversion
  LF/CRLF du manifeste de stratification.

Une première vérification PowerShell a réussi avant la dernière correction
des fonctions de transport. Elle n'est pas présentée comme une validation
de l'état final : les deux vérificateurs ont ensuite été relancés sur cet
état, sans build concurrent. Aucun audit indépendant, commit, push ou
changement de branche n'a été réalisé.

## 22. Échange local indépendant et continuations typées

Ce sous-lot poursuit A3 sur la loi locale calibrée déjà déclarée. Il ne ferme
ni tout A3 ni la reconstruction relativiste. Les quatre fondations, le maître
de calcul, sa machine, les contrats antérieurs et la cible restent inchangés.

### Critère d'indépendance construit

Les deux instructions prennent leurs ports dans un même curseur déjà formé.
La seconde instruction de chaque ordre est transportée par l'inclusion des
anciennes références. Elle ne peut donc pas lire la sortie fraîche de la
première. La loi locale ajoute une ressource sans modifier les anciennes :
les deux instructions peuvent partager un ancien port en lecture.

Ce critère est une classe suffisante d'échanges du candidat local, pas une
définition exhaustive de l'indépendance physique. Il est plus restrictif que
la simple absence d'une arête affichée. `InputPort.priorOrigin` construit,
pour chaque port de l'instruction affaiblie, son port source et le raccord
exact ; `InputPort.prior_not_fresh` exclut positivement une entrée fraîche.

`produceIndependentPair` exécute les deux productions dans l'ordre, une fois
chacune, et conserve leurs deux déterminations positives.
`IndependentPairProduction.execution` assemble leur histoire depuis ces
données conservées, sans appeler le producteur. `independentPair_runner_exact`
raccorde cette exécution au runner existant. Pour comparer les deux ordres,
on exécute chaque ordre ; cette comparaison n'est pas une affirmation qu'une
seule course accomplirait simultanément les deux histoires.

### Occurrences, rôles et dépendances

[ReferenceRenaming](../../RelationalPerimeter/Relativity/Production/ReferenceRenaming.lean)
construit des correspondances de références préservant leur sorte et leurs
deux lois de retour. Le transport des occurrences utilise `ExactTypeTransport`.
Les deux sorties fraîches sont échangées, les anciennes occurrences restent
les mêmes, et aucune égalité de lectures ne sert à identifier des sources.

[IndependentExchange](../../RelationalPerimeter/Relativity/Production/IndependentExchange.lean)
consomme les productions conservées des deux ordres. La correspondance de
lectures est démontrée depuis leurs rôles d'action. Le transport des arêtes
`Used` élimine ces rôles et leurs ports : l'arête fraîche du second ordre
correspond à l'arête héritée de l'autre, et réciproquement. Les anciennes
arêtes gardent leurs témoins de la formation initiale. Il ne suffit pas de
permuter des indices d'un graphe fourni séparément.

`ConstitutedRaccord` conserve cette lecture et deux fonctions exécutables
qui transportent les témoins d'arêtes dans les deux directions. `used_iff`
prouve l'équivalence de leur existence aux occurrences correspondantes ;
`forwardPath` transporte les chemins composés. La réalisation concrète
`independentPairConstitution` ferme ces champs sur les productions retenues
de la paire, sans demander une hypothèse extérieure de commutation.

Les histoires et les frontières intermédiaires ne sont pas égalées : un
ordre a accompli A tandis que l'autre a accompli B. Le client public démontre
explicitement une différence de sortes intermédiaires. La correspondance
finale concerne le même ensemble de productions accomplies.

### Prolongement sans réexécution

[TransportedContinuations](../../RelationalPerimeter/Relativity/Production/TransportedContinuations.lean)
transporte tout programme local typé de longueur finie arbitraire. Chaque
étape consomme les deux productions locales de ses présentations puis étend
le raccord par leurs sorties fraîches. `afterProduction` reçoit les résultats
déjà exécutés ; `prefixProduction` assemble l'histoire conservée.

`continueCorresponding_source_exact` et `continueCorresponding_target_exact`
prouvent l'égalité des résultats complets, histoire comprise, avec le runner
existant sur chaque programme correspondant. `Program.rename_returns` prouve
le retour du programme, pas seulement celui de son résultat numérique.
Les ports des étapes futures sont transportés structurellement ; aucune
valeur produite par une continuation achevée n'est reçue par la tête.

`transported_inspection_exact` préserve la lecture locale complète d'une
occurrence correspondante, y compris la liste des incréments d'un signal.
Il ne prétend pas préserver une inspection à une adresse non transportée.

### Contrôle négatif et obligation encore ouverte

Le [client public](../../Tests/Relativity/IndependentExchangeChecks.lean)
construit une émission suivie d'un relais qui lit réellement cette émission.
Il prouve que cette instruction ne peut être l'affaiblissement d'une
instruction sur le contexte antérieur : elle ne satisfait donc pas le
critère d'échange construit. Le client conserve aussi deux sorties aux
valeurs égales mais aux occurrences distinctes.

Ce sous-lot ne prouve pas encore la préservation de toutes les observations
du contrat **adressé** de A3. `LocalRequest` contient des adresses numériques,
des inspections, des actions et des refus. Après échange, une même adresse
peut désigner une autre occurrence ou une autre sorte. Le client réfute
expressément l'équivalence future des deux présentations lorsque les
adresses ne sont pas transportées.

La prochaine obligation est donc de transporter les demandes et leurs
admissions/refus étape par étape, depuis le raccord effectivement conservé,
puis de prouver l'égalité des rapports pour toutes leurs listes finies.
Elle ne peut être remplacée par l'accord des seuls programmes admis ou par
un contrat réduit. Aucun contrat existant n'est modifié dans ce sous-lot.
Les influences physiques admissibles, rencontres, regroupements autorisés,
présentations/raffinements, géométrie et reconstruction restent ouverts.

### Vérification du sous-lot

La compilation du nouveau client public et les audits de ses déclarations
réussissent. Les évaluations locales d'exécutabilité ne constituent pas des
mesures ni des expériences physiques.

La lecture du C généré a révélé une première version du transport d'arêtes
qui reconstruisait ses déterminations. Cette version a été corrigée avant
livraison : les transports consomment désormais `IndependentPairProduction`.
La vérification globale de l'état antérieur à cette correction ne vaut pas
validation de l'état final. Les résultats des gates finales sont consignés
ci-dessous après leur exécution.

- `bash scripts/verify.sh`, puis `pwsh -NoProfile -File scripts/verify.ps1`,
  exécutés séquentiellement sous Windows sur l'état corrigé : réussite sur
  les mêmes 271 fichiers Lean et les 23 fixtures attendues, avec leurs sites
  de diagnostic exacts. Le build complet réussit en 273 jobs, sans
  avertissement Lean.
- Audit exhaustif : 22 257 constantes, 270 modules importés, aucune exception
  écrite à la main ; 364 exceptions générées classifiées par les règles
  existantes inchangées. Les blocs finaux des nouvelles déclarations
  n'affichent aucun axiome ; un seul bloc final dans chaque fichier Lean.
- Stratification : 223 modules de production, tous contraints et accessibles,
  aucun orphelin. Les nouveaux modules occupent `H3`, `H4` et `H5` ; la façade
  reste en `H6`. Les contrôleurs de stratification ne sont pas modifiés par
  ce sous-lot.
- Contrôles scientifiques statiques, clients Lean du registre, frontières
  d'import et code compilé du maître existant : réussite. Les revues ouvertes
  restent ouvertes ; aucune empreinte du registre n'est actualisée.
- Lecture du C final : `produceIndependentPair` contient les deux seuls
  appels à `execute` de son module. L'assemblage de l'histoire et les
  transports d'arêtes ne contiennent aucun appel au producteur. Le runner
  des continuations appelle `perform` une fois par présentation dans sa
  branche d'action, transmet les résultats conservés à `afterProduction`,
  puis reprend depuis leurs successeurs réels. Cette lecture locale n'est
  pas une preuve de coût physique ou une gate générale du compilateur.
- Comparaison SHA-256 avec le début du sous-lot : aucune suppression.
  Seuls quatre nouveaux fichiers Lean, leur façade, leur import d'audit,
  les trois lignes du manifeste et ce plan changent. Les fondations, les
  sources du maître et de la machine, les utilitaires numériques, tous les
  contrats antérieurs, la configuration et le registre restent identiques.
- Scan des constructions interdites et `git diff --check` : réussite.
  Le seul avertissement Git porte sur la conversion LF/CRLF du manifeste,
  pas sur un défaut de preuve ni du diff.

Ces résultats valident le sous-lot décrit, pas les obligations ouvertes
du contrat transporté ni la cible relativiste finale. Aucun audit extérieur,
commit, push ou changement de branche n'a été réalisé.

## 23. Transport du contrat local adressé complet

Ce sous-lot ferme l'obligation laissée ouverte en section 22 : transporter
les demandes locales, leurs admissions et leurs refus, puis tous leurs
rapports finis. Il conserve exactement `LocalRequest`, `LocalAdmission`,
`localContract` et le runner `runRequests`. Il ne remplace pas le contrat par
les seules demandes admises ou par une lecture du seul résultat final.

### Des occurrences aux adresses, pas l'inverse

[AddressTransport](../../RelationalPerimeter/Relativity/Production/AddressTransport.lean)
associe au transport de références une permutation des adresses naturelles
avec ses deux lois de retour. Son champ `positions` raccorde chaque adresse
à sa référence typée effectivement transportée. Le raccord inverse est
prouvé, puis les témoins `ReferenceAt` et `LocalAdmission` sont transportés
positivement. Les adresses ne constituent pas de nouvelles occurrences.

Le cas concret échange les deux adresses fraîches et fixe toutes les autres,
y compris celles qui ne désignent aucun port. Lorsqu'une action ajoute une
ressource, `extend` conserve son adresse fraîche zéro et décale le transport
des anciennes occurrences. Une demande garde son constructeur et sa sorte
d'inspection. Un mauvais type de port ou un port absent reste donc un refus
de cette demande correspondante ; il n'est pas remplacé par un autre opcode.
`transported_admission_exact` établit l'égalité des décisions booléennes à
partir des témoins positifs ou de leur réfutation.

### Productions partagées et raccord suivant

[TransportedRequests](../../RelationalPerimeter/Relativity/Production/TransportedRequests.lean)
raccorde ce transport d'adresses aux lectures et aux deux transports
positifs des arêtes constituées. `independentPairAddressed` ferme cette
interface sur les deux ordres réellement produits du candidat local.

`pairedRequest` décide l'admission dans la première présentation. Un témoin
admis détermine les ports correspondants dans l'autre présentation. Chaque
action est alors produite une fois dans chaque présentation ; les mêmes
sorties sont utilisées par les événements, les successeurs, les histoires
et `afterProduction`. Inspection et refus n'ajoutent aucune production.
L'absence de demande de futur dans cette fonction reste explicite dans
son type. Comparer deux présentations exécute deux courses : cela ne signifie
pas qu'une course réaliserait simultanément les deux ordres.

`pairedRequest_source_exact` et `pairedRequest_target_exact` prouvent
l'égalité des réponses complètes avec `performRequest`, histoire comprise.
L'unicité des références à une position fixée permet de raccorder les témoins
transportés aux témoins retournés par le résolveur existant. Les consommateurs
des histoires et des dépendances ne relancent pas le producteur.

### Toutes les listes finies du même contrat

`runCorrespondingRequests` traite structurellement toute liste finie,
avec tous les entrelacements des actions, inspections et refus. La suite
reçoit les deux curseurs réellement produits et leur raccord courant.
Chaque demande traduite vient du transport de sa propre étape, pas d'une
permutation initiale appliquée après coup à toute la liste.

Les théorèmes `correspondingRequests_source_exact` et
`correspondingRequests_target_exact` raccordent les résultats complets aux
deux appels du runner inchangé. `transported_all_futures_exact` établit
l'égalité des rapports du contrat, admissions et refus compris. Il est
quantifié sur toute liste finie ; appliqué au raccord inverse, il couvre
aussi toute liste demandée dans l'autre présentation. `translated_length_exact`
garantit qu'aucune demande n'est omise. Les lois de retour des demandes sont
établies pour chaque raccord courant ; cette section ne revendique pas une
égalité des objets fonctionnels de raccord ni une preuve séparée de retour
du runner complet par double exécution.

Le [client public](../../Tests/Relativity/TransportedRequestChecks.lean)
consomme ces théorèmes via le seul import public. Il vérifie un mélange
d'inspections, réception, relais, émission, mauvais port et adresse absente,
avec leurs traductions évolutives exactes. Il conserve et transporte une
arête et son chemin depuis la production initiale jusqu'au curseur final.
Il prouve aussi qu'une traduction figée avant une nouvelle production peut
modifier l'admission et donc le contrat. Les évaluations sont seulement des
smoke checks d'exécutabilité, pas des mesures de coût ni des expériences.

### Portée et obligations suivantes

Ce résultat concerne les échanges indépendants construits en section 22,
sous la loi locale calibrée déclarée, et ce contrat local complet. Il ne
donne pas l'équivalence de demandes aux mêmes adresses non transportées ;
ce serait faux. Il ne définit ni les influences physiques admissibles
générales, ni les rencontres, ni le regroupement autorisé, ni des coordonnées
d'espace-temps. Ces obligations, les présentations et raffinements,
la génération du domaine continu, la métrique et la reconstruction exacte
de la théorie relativiste restent ouvertes. La cible n'est pas remplacée
par ce résultat intermédiaire.

### Vérification de ce sous-lot

La compilation du client public réussit sans avertissement et tous les noms
de ses audits sont sans axiome. Les deux rapports évalués donnent les mêmes
neuf admissions/refus et trois productions réelles. Le scan de tous les
274 fichiers Lean ne trouve aucune construction interdite ; chaque fichier
contient exactement un bloc d'audit final.

- `lake build` : réussite en 276 jobs, aucun avertissement Lean.
- `bash scripts/verify.sh`, puis `pwsh -NoProfile -File scripts/verify.ps1`,
  exécutés séquentiellement sous Windows : réussite sur les mêmes 274 fichiers
  Lean et 23 fixtures d'échec, avec diagnostics et sites exacts.
- Audit exhaustif : 22 429 constantes, 273 modules importés, zéro exception
  écrite à la main ; les 364 exceptions générées restent classifiées par les
  règles existantes inchangées.
- Stratification : 225 modules de production, tous contraints et accessibles,
  aucun orphelin. Les deux nouveaux modules occupent `H4` et `H6` ; la façade
  passe en `H7`. Les deux contrôleurs étendent explicitement cette seule borne
  et gardent les imports strictement descendants. Ils n'autorisent aucun
  import du maître ou de la machine dans les strates locales.
- Contrôles scientifiques statiques et Lean du registre, contrôles compilés
  de la chaîne maître existante : réussite. Les revues ouvertes demeurent
  ouvertes et aucune empreinte du registre n'a été actualisée.
- Lecture du C généré : les trois branches d'action de `pairedAdmitted`
  contiennent chacune exactement deux appels à `perform`, un par
  présentation. Inspection et refus n'en contiennent aucun. Le module
  `AddressTransport`, les assemblages de réponses et d'histoires et les
  raccords consommateurs n'appellent ni `perform` ni `execute`. Le runner
  reprend depuis les deux successeurs du résultat partagé. Cette inspection
  locale n'est ni un contrôleur général de tout le code compilé ni une borne
  de coût physique.
- Comparaison SHA-256 avec le début du sous-lot : trois fichiers Lean ajoutés,
  aucune suppression. Seuls la façade locale, son client d'audit exhaustif,
  les deux contrôleurs de stratification, leur manifeste et ce plan évoluent.
  Les fondations, le maître, la machine, les utilitaires numériques, les
  contrats antérieurs, la cible canonique, la configuration Lean et le
  registre restent identiques.
- `git diff --check` : réussite ; le seul avertissement Git concerne la
  conversion LF/CRLF du manifeste.

Aucun audit indépendant, commit, push ou changement de branche n'a été
réalisé. Ces contrôles valident ce sous-lot, pas les obligations relativistes
encore ouvertes.

## 24. Influences locales permises et provenance des arrivées

Ce sous-lot poursuit A1 et A2 sur la loi locale déjà déclarée. Il ne complète
pas encore les rencontres physiques ni la relation générale d'influence du
domaine à construire. Les primitives restent émission, relais et réception ;
aucune interaction binaire ni géométrie n'est ajoutée en les renommant.

### Possibilité locale, puis production effective

[InfluencePlans](../../RelationalPerimeter/Relativity/Production/InfluencePlans.lean)
construit `InfluencePlan` dans `Type` à partir des ports de la loi. Un plan
peut suivre une sortie fraîche ou conserver son origine à travers une
production intermédiaire. Son type reçoit les sortes et l'occurrence source,
pas un curseur futur ni une valeur finale imposée. Il décrit un futur permis
de cette loi, non un événement qui aurait déjà eu lieu. La cible est une
production future de la sorte déclarée ; ce n'est pas une référence arbitraire
à un événement présent que l'on prétendrait rendre causal après coup.

`instructionAdmission` construit les références positives de chaque demande
correspondante. `instruction_request_enabled` raccorde ce témoin au résolveur
inchangé. Les plans n'autorisent aucune instruction supplémentaire : par
exemple, `target_not_payload` refute une cible produite de sorte `payload`,
que la loi actuelle ne sait pas produire.

`realizeInfluenceFrom` partage une production à chaque instruction. La suite
reçoit son successeur réel. Le résultat contient les valeurs finales,
l'histoire fondée et un `UsedPath` entre l'origine transportée et la cible
effectivement produite. Les chemins se composent à partir des rôles positifs
conservés, non depuis les positions numériques. Le raccord point par point
`historyTransport_append_occurrence` justifie la composition des références.
`realizeInfluence_execution_exact` prouve que l'effacement du chemin retrouve
exactement `run`, histoire comprise. Cette égalité est une preuve de raccord,
pas une seconde exécution ajoutée au chemin opérationnel.

Les plans sont ici construits par leurs témoins de ports. Ce sous-lot ne
revendique pas un chercheur physique qui découvrirait toutes les influences
possibles, ni la complétude d'une décision d'absence d'influence. L'absence
d'une arête exécutée ne constitue toujours pas une séparation spatiale.

### Provenance positive, sans rejouer les actions

[SignalJourneys](../../RelationalPerimeter/Relativity/Production/SignalJourneys.lean)
retrouve l'origine émise et les relais d'un signal en éliminant sa formation
enregistrée. `EmissionOccurrence` conserve positivement l'émission propre ;
`SignalJourney` conserve ses relais et les productions intercalées.
`originEvent` construit le témoin d'émission à sa référence transportée.
`reaches` fournit soit l'origine elle-même, soit le chemin de dépendances
effectivement utilisé. Le nombre de relais égale la longueur du registre
d'incréments, et le payload est conservé depuis cette origine.

`receptionJourney` consomme la production de réception déjà obtenue et
conserve la provenance du signal dans son successeur réel.
`reception_reads_arriving_signal` rattache la lecture reçue à ce signal.
Ni l'extracteur de provenance ni ce consommateur d'arrivée n'appellent le
producteur. Deux signaux de même valeur peuvent avoir deux émissions
constituées distinctes ; leur lecture égale ne fusionne pas ces sources.
Ces lois portent sur le candidat local, pas encore sur des trajectoires
d'espace-temps ou une mesure physique du temps propre.

### Transport de la possibilité et raccord aux exécutions

[TransportedInfluences](../../RelationalPerimeter/Relativity/Production/TransportedInfluences.lean)
transporte positivement les ports, l'origine et toute la suite du plan.
`transported_influence_iff` conserve sa possibilité dans les deux sens.
`renamed_schedule` raccorde cette construction au transport des programmes,
avec leur loi de retour. Comparer les exécutions effectives requiert en
plus le raccord constitué des lectures et arêtes : une permutation de
références seule ne garantit pas l'accord des ressources physiques reçues.
`corresponding_influence_executions` ferme ce raccord sur les runners déjà
existants ; ce théorème ne lance pas deux fois un même parcours.

Le [client public](../../Tests/Relativity/InfluenceChecks.lean) construit une
émission suivie d'un nombre fini arbitraire de relais et d'une réception.
Sa longueur exécutée est prouvée pour toute entrée reçue et tout nombre de
relais. Les exemples fermés vérifient aussi une production intercalée,
deux émissions égales mais distinctes, la provenance d'une arrivée et le
transport des plans par l'échange indépendant existant. Les évaluations
sont exclusivement des smoke checks d'exécutabilité.

### Limite précise et prochaine obligation

Une rencontre physique ne peut pas être déduite de la seule coexistence
de deux réceptions. Elle exige une production d'interaction et ses ports,
sa loi et ses effets futurs admissibles. La loi actuelle ne la définit pas.
Cette obligation reste donc ouverte, comme le regroupement autorisé,
les présentations et raffinements, la génération du domaine continu,
la métrique, la dynamique et la reconstruction relativiste exacte.
La cible de la section 1 et les résultats du maître restent inchangés.

### Vérification de ce sous-lot

La compilation des trois modules et du client public a réussi sans
avertissement et sans axiome dans leurs blocs d'audit. L'état final a été
vérifié par les contrôles suivants :

- `lake build` : réussite en 280 jobs, aucun avertissement Lean.
- `bash scripts/verify.sh`, puis `pwsh -NoProfile -File scripts/verify.ps1`,
  exécutés séquentiellement sous Windows : réussite sur les mêmes 278 fichiers
  Lean et 23 fixtures d'échec, avec diagnostics et sites exacts.
- Audit exhaustif : 22 685 constantes dans 277 modules importés, zéro
  exception écrite à la main. Les 364 exceptions générées restent classifiées
  par les règles existantes, inchangées.
- Stratification : 228 modules de production, tous contraints et accessibles,
  aucun orphelin. Les trois nouveaux modules sont classés `H4`, `H4` et `H6`.
  Les contrôleurs de stratification ne sont pas modifiés dans ce sous-lot.
- Contrôles scientifiques statiques et Lean du registre, frontières d'import
  et contrôles compilés du maître et de la machine : réussite. Les revues
  ouvertes restent ouvertes ; aucune empreinte du registre n'est actualisée.
- Lecture du C final : `realizeInfluenceFrom` contient un seul appel à
  `perform` dans chacune de ses trois branches. La continuation reçoit les
  champs du successeur partagé. L'assemblage d'histoire consomme ce résultat
  conservé. `SignalJourneys` et `TransportedInfluences` ne contiennent aucun
  appel au producteur ou au runner. Cette inspection locale ne constitue
  ni une gate générale du compilateur ni une borne de coût physique.
- Comparaison SHA-256 avec le début du sous-lot : quatre fichiers Lean
  ajoutés, aucune suppression. Seuls la façade locale, l'import du client
  dans l'audit exhaustif, les trois lignes du manifeste et ce plan évoluent.
  Les quatre fondations, le maître, la machine, les modules numériques,
  les contrats antérieurs, la configuration, la cible canonique et le
  registre restent identiques.
- Scan des constructions interdites : absence totale. Exactement un bloc
  d'audit final dans chaque fichier Lean. Les 45 liens locaux du plan sont
  valides ; aucune espace terminale dans les quatre nouveaux fichiers.
  `git diff --check` réussit ; son avertissement LF/CRLF sur le manifeste
  n'est pas un défaut de contenu.

Aucun audit indépendant, commit, push ou changement de branche n'a été
réalisé. Ce sous-lot est vérifié dans la portée précisée ci-dessus ; il
ne ferme pas les obligations physiques et relativistes encore ouvertes.

## 25. Réceptions admises et première interaction instrumentale

Ce sous-lot poursuit A1 à partir des productions du sous-lot 24. Il ajoute
une loi instrumentale explicitement déclarée : comparer deux lectures
réellement reçues en produisant la seconde moins la première. Cette loi
n'est pas déduite d'une géométrie, mais elle n'est pas non plus présentée
comme une loi physique de rencontre déjà reconstruite. Aucune colocalisation,
coordonnée, distance, simultanéité ou métrique n'est admise par ce raccord.
La cible de la section 1 reste inchangée.

### Reconnaître une arrivée dans sa constitution

[ArrivalContexts](../../RelationalPerimeter/Relativity/Production/ArrivalContexts.lean)
définit `Arrived` dans la formation effective. Son constructeur de réception
lie la nouvelle lecture au signal exact qui l'a produite. Son constructeur
de transport conserve cette réception à travers les productions suivantes.
`usedEdge` retrouve l'arête effectivement utilisée ; `reading_exact` relie
les valeurs sans identifier les occurrences. `signal_unique` prouve que
cette lecture reçue ne peut pas se voir attribuer un autre signal source.

`arrivalOfProduction` consomme la réception conservée, sans la relancer.
`historyTransportArrival` prolonge positivement ce témoin dans l'histoire
réellement exécutée. `findArrival` et `resolveArrivalAt` inspectent cette
formation, pas les valeurs seules : ils construisent une arrivée ou en
réfutent l'existence à l'adresse demandée. Une lecture initiale fournie
est refusée comme arrivée, même si sa valeur est égale à celle d'une réception.
Cette recherche porte sur une provenance déjà constituée ; elle ne constitue
ni un chercheur de transformations physiques ni une décision d'absence
universelle d'influence.

`transported_given_reading_not_arrived` ferme aussi ce refus après toute
histoire locale : conserver une lecture initiale dans un support plus riche
ne la transforme jamais rétrospectivement en réception. Le client vérifie
ce refus après deux réceptions, alors même que les valeurs comparées sont
égales. La disponibilité et l'égalité numérique ne suffisent donc pas à
autoriser les ports de cette interaction.

### Produire une comparaison, puis consommer sa sortie

[ArrivalComparisons](../../RelationalPerimeter/Relativity/Production/ArrivalComparisons.lean)
exige deux références de réception distinctes et leurs témoins positifs.
`decideComparison` vérifie les adresses, les réceptions et leur distinction.
La demande est refusée si un port n'est pas une arrivée ou si les deux ports
désignent la même occurrence. Cette admission n'utilise aucune égalité de
coordonnées ; elle est exactement celle de la nouvelle loi instrumentale,
pas une admission de rencontre dans l'espace-temps.

`compareArrivals` consomme les témoins des lectures effectivement reçues.
`ComparisonProduces` détermine son résultat ; aucun résultat numérique
prescrit indépendamment n'entre dans cette production. `lower_exact`
raccorde cette consommation aux deux ports du producteur de ressources.
La nouvelle formation réemploie le même support fondationnel et sa formation
antérieure, sans nouvelle racine `given` ni producteur arbitraire.
Les arêtes `comparison_first_used` et `comparison_second_used` relient les
deux réceptions à la lecture nouvelle ; `comparison_first_reception_kept`
conserve aussi l'arête entre le premier signal et sa réception.

`InstrumentFormation` est l'extension fermée de la loi locale pour ce lot :
une comparaison de deux arrivées, puis les instructions existantes
d'émission, de relais et de réception. Elle n'est pas une deuxième fondation
ni une modification silencieuse de `Formed`, qui désigne toujours la loi
antérieure. `InstrumentInterpretation` raccorde ses mêmes rôles au même
`Formation` générique. Les pas de continuation réemploient l'histoire
fondée `StrongPerimetralTurning.History` et les références typées existantes.

`runCompared` produit et conserve la comparaison avant sa continuation.
La continuation reçoit son successeur effectif ; aucune valeur future
ni histoire terminée n'entre dans la production de tête.
`compared_head_independent` prouve l'identité de cette tête pour deux suites
de continuation différentes. C'est une propriété de construction et de
dépendance, pas une définition du temps physique. `runInstrument` exécute
les instructions sur cette formation élargie ; sa longueur est prouvée
pour tout programme fini. `emitComparison` donne un consommateur concret
de la lecture partagée : l'émission ne refait pas la comparaison.

`ComparisonExecution.transport` conserve toutes les lectures et distinctions
anciennes dans le résultat continué. Le transport des arêtes exécutées est
positif et consomme les rôles conservés. Un résultat de comparaison nul
n'identifie ni les réceptions ni leurs émissions ou parcours.

### Instance fermée et vérifications de sens

Le [client public](../../Tests/Relativity/ArrivalComparisonChecks.lean)
construit deux émissions distinctes, une première réception, puis un nombre
fini arbitraire de relais et la seconde réception. Les arrivées ne sont
pas fournies par l'entrée : elles sont produites par le même interprète local.
Le nombre de relais n'est pas une borne de longueur du cadre.

Sans relais supplémentaire, deux lectures égales produisent une comparaison
nulle tout en restant deux occurrences distinctes. Avec un relais calibré,
la comparaison change. Les origines émises demeurent distinctes et leurs
témoins sont conservés. Une émission puis une réception de cette comparaison
consomment la sortie partagée. Les tests généraux portent aussi sur la
longueur arbitraire, la conservation des anciens ports, leurs distinctions,
leurs dépendances et l'indépendance de la tête envers la continuation.
Les évaluations sont uniquement des smoke checks d'exécutabilité.

### Portée restante, sans substitution

Ce lot fournit une première production d'interaction instrumentale entre
deux arrivées constituées et une continuation qui la consomme. Il ne ferme
pas encore l'obligation d'une rencontre physique relativiste. Le contrat
adressé antérieur n'est ni élargi ni revendiqué sur `InstrumentCursor` :
le contrat complet de cette extension, son transport entre présentations
et les comparaisons successives restent à construire explicitement.
Les sources distinctes ne sont pas regroupées dans ce lot.

Restent donc ouverts le regroupement physique autorisé, les présentations
et raffinements pertinents, la génération du domaine continu, la métrique,
la dynamique et la reconstruction exacte de la relativité. La comparaison
arithmétique n'est pas leur substitut. Les fondations, la cible canonique,
le maître computationnel, la machine et leurs contrats demeurent inchangés.

### Vérifications effectuées sur le lot

- `lake build` réussit en 283 jobs. La gate finale reprend ce build sur
  l'état final, sans avertissement Lean.
- `bash scripts/verify.sh`, puis `pwsh -NoProfile -File scripts/verify.ps1`,
  exécutés séquentiellement sous Windows, réussissent sur les mêmes
  281 fichiers Lean et les 23 fixtures d'échec, avec diagnostics et sites
  exacts. Les contrôles statiques et Lean du registre et les contrôles
  compilés existants réussissent ; leurs revues restent ouvertes.
- L'audit exhaustif couvre 23 221 constantes dans 280 modules importés :
  aucune dépendance axiomatique écrite à la main. Les 364 exceptions
  générées restent classifiées par les règles antérieures, inchangées.
- Les 230 modules de production sont classifiés, contraints et accessibles,
  sans orphelin. Les deux ajouts sont respectivement `H5` et `H6` ; aucun
  contrôleur de stratification n'est modifié dans ce lot.
- L'examen du C des chemins nouveaux confirme : une seule comparaison
  dans `performComparison`, une seule tête de comparaison dans `runCompared`,
  un seul `execute` dans `performInstrument` et une seule production par pas
  dans `runInstrumentFrom`. Les successeurs et l'histoire consomment les
  déterminations partagées. Le raccord de formation de comparaison construit
  le producteur et son témoin sans refaire la soustraction ; l'extraction
  d'arrivée n'appelle aucun producteur ou runner. Il s'agit d'une inspection
  locale du code généré, pas d'une gate générale ou d'un coût physique prouvé.
- La comparaison SHA-256 avec le début du lot constate trois fichiers Lean
  ajoutés, aucune suppression, et seulement quatre fichiers existants modifiés :
  la façade locale, l'import du client dans l'audit exhaustif, le manifeste
  de stratification et ce plan. Tous les autres fichiers, dont les quatre
  fondations, le maître, la machine, les contrats, les modules numériques,
  la configuration, la cible canonique et le registre, restent identiques.
- Chaque fichier Lean conserve exactement un bloc d'audit final ; les
  constructions interdites et les espaces terminales des nouveaux fichiers
  sont absentes. Les liens locaux du plan et `git diff --check` sont vérifiés.
  L'avertissement Git LF/CRLF sur le manifeste n'est pas un avertissement Lean.

Aucun commit, push, changement de branche ou audit indépendant n'est réalisé.
La branche reste `relativite`. Ce lot est vérifié dans la portée instrumentale
ci-dessus ; la cible relativiste finale n'est pas encore établie.

## 26. Contrat explicite des futurs après la comparaison

Ce lot poursuit le raccord à A4 pour la loi instrumentale de la section 25.
Il ne change ni la cible de la section 1 ni le contrat signal-only antérieur.
Il fixe, avant tout regroupement, les demandes que peut recevoir le support
effectivement produit par une comparaison : émission, relais, réception et
inspection typée, dans toute liste finie et tout entrelacement de ces demandes.
Les refus appartiennent au même contrat et ne produisent aucune ressource.

### Admission, effet et successeur sur le même support

[InstrumentFutures](../../RelationalPerimeter/Relativity/Production/InstrumentFutures.lean)
définit `InstrumentAdmission` et `decideInstrumentAdmission` sur les sortes
et références de l'`InstrumentCursor` actuel. Le décideur construit les ports
positifs ou leur réfutation ; il ne reçoit pas d'oracle d'admission et ne
consulte pas une histoire future. Les adresses sont des sélecteurs locaux
d'occurrences, pas des positions dans l'espace-temps.

`instrumentContract` fixe ces demandes et leurs événements. Il réemploie
`LocalRequest`, `LocalEvent`, `LocalReadout` et `FutureContract` sans convertir
la nouvelle formation en un ancien curseur ou reconstruire une racine reçue.
L'inspection d'un signal expose son enregistrement complet, notamment sa
liste d'incréments ; elle ne réduit pas un parcours à sa dernière lecture.
Il n'y a pas d'observation passive supplémentaire : les lectures sont les
événements des demandes explicites. Cette portée est fixée ici, non choisie
après un résultat de regroupement.

`performInstrumentAdmitted` appelle une seule production dans chaque branche
d'action. La détermination conservée fournit l'événement, le successeur et
le pas de l'histoire fondée. `performInstrumentRequest` prend une seule
décision locale ; inspection et refus gardent le curseur et l'histoire racine.
Les fonctions séparées `instrumentReferenceNext` et `instrumentReferenceEvent`
sont la spécification, pas l'évaluateur exécutable à paire partagée.

`runInstrumentRequests` consomme cette paire de tête puis exécute la suite
depuis son successeur réel. `instrument_all_futures_exact` prouve l'accord
des événements, droits et lectures pour toutes les listes finies du contrat,
y compris les refus ; `instrument_final_cursor_exact` raccorde aussi le
curseur final à la suite spécifiée. `instrument_request_history_bound`
borne le nombre de productions enregistrées par le nombre de demandes.
Ce n'est ni une borne de travail, ni une mesure de temps physique : le coût
de la résolution des ports et des actions n'est pas compté par ce théorème.

### Tête partagée et continuation effective

`runComparedRequests` produit d'abord la comparaison et donne son support
effectif au runner de demandes. `compared_requests_head_independent` concerne
la tête entière, sans dépendance envers la suite future. Les lectures du
contrat consomment donc une comparaison déjà constituée, pas une valeur
prescrite indépendamment.

Une reprise utilise `InstrumentRequestedExecution.continue` sur le curseur
conservé ; elle ne rappelle pas `runComparedRequests`. `continuedHistory`
compose les histoires stockées. Le transport de support et `transportUsed`
conservent positivement les anciennes références et les arêtes produites.
`compared_requests_keep_sources` conserve la distinction des deux réceptions
sources après n'importe quelle suite de demandes. Aucune égalité de valeur
n'est promue en identité d'événements.

### Séparateur futur qui interdit un oubli prématuré

Le [client public](../../Tests/Relativity/InstrumentFutureChecks.lean)
construit deux émissions et leurs deux réceptions, puis une comparaison.
Il vérifie l'émission de sa sortie partagée, les refus de ports absents ou
de mauvaise sorte, les événements et le successeur correspondants. Sa suite
entrelacée a trois productions ; une reprise à partir du résultat en ajoute
deux, sans reconstruire la comparaison. Une preuve porte aussi sur un nombre
arbitraire de lectures répétées : aucune production n'y est ajoutée.

Un autre consommateur émet la sortie, la relaie deux fois, la reçoit puis
réémet la même lecture. Les deux signaux finaux ont exactement la même lecture
numérique, mais leurs listes d'incréments diffèrent. La demande d'inspection
du signal les sépare dans ce même contrat. Le théorème générique
`instrument_futures_preserve_readout` extrait cette condition nécessaire
d'une égalité de tous les futurs ; le client ferme sa réfutation sur ces
deux exécutions. Ce n'est pas une identité des sources, ni une minimalité
physique universelle, ni une autorisation d'effacer les chemins.

### Limite et prochaine obligation

Le contrat fermé ici est celui du sous-lot : une comparaison déjà produite,
puis les trois instructions signal et leurs inspections. Les comparaisons
successives ne sont pas dans cette grammaire ; leurs formations et admissions
doivent être construites avant de revendiquer leur contrat. Le contrat
physique final de A4 n'est donc pas annoncé fermé. Son transport entre
présentations, les interactions répétées et les futurs supplémentaires
restent des obligations explicites. Aucun regroupement ou oubli mémoire
n'est ajouté dans ce lot.

La suite doit prolonger ces déterminations et leurs admissions, puis fermer
l'autorisation de regroupement relativement au contrat physique fixé. Elle
ne peut pas utiliser l'égalité d'une seule lecture pour effacer une différence
de parcours que la continuation précédente révèle. Génération du domaine,
continuité, métrique, dynamique et reconstruction exacte de la relativité
restent ouvertes. Fondations, maître, machine, contrats acquis et cible
canonique demeurent inchangés.

### Vérification de ce lot

La compilation ciblée du nouveau module et du client réussit sans avertissement
et sans axiome dans leurs déclarations auditées. Les évaluations sont des
smoke checks uniquement : admission/refus `(true, false)`, trois puis cinq
productions, et lectures de longueurs de chemin `(some 2, some 0)`.

- `lake build` réussit en 285 jobs sans avertissement Lean. Les deux gates
  complètes reprennent ce build sur l'état final.
- `bash scripts/verify.sh`, puis `pwsh -NoProfile -File scripts/verify.ps1`,
  exécutés séquentiellement sous Windows, réussissent sur les mêmes 283
  fichiers Lean et les 23 fixtures d'échec, pour leurs diagnostics et sites
  exacts. Les contrôles statiques et Lean du registre et les contrôles
  compilés existants réussissent ; les revues du registre restent ouvertes.
- L'audit exhaustif couvre 23 361 constantes dans 282 modules importés,
  avec 364 exceptions générées et aucune exception écrite à la main.
  Aucune règle de classification de ces exceptions n'est modifiée.
- Les 231 modules de production sont classifiés, contraints et accessibles,
  sans orphelin. Le contrat nouveau est `H7`, sa façade `H8`. L'ajout du rang
  `H8` dans les deux checkers ne change pas la règle d'import strictement
  descendant, ni l'interdiction de dépendre du maître ou de la machine.
  Les rangs numériques et les autres strates restent inchangés.
- La lecture des corps complets du C généré confirme une seule production
  par branche d'action dans `performInstrumentAdmitted`, une seule décision
  dans `performInstrumentRequest`, et une seule paire de tête par pas du
  runner. `instrumentProductionHistory` lit la détermination stockée sans
  appeler un producteur. `runComparedRequests` forme une seule comparaison
  avant la continuation ; `.continue` reprend depuis le curseur conservé
  sans rappeler cette comparaison. Cet examen est local, pas une gate
  générale de code compilé ni une preuve de coût physique.
- Chaque fichier Lean possède un seul bloc d'audit final. Le scan des
  constructions interdites, les espaces terminales des nouveaux fichiers,
  les 55 liens locaux du plan et `git diff --check` sont vérifiés. Le seul
  avertissement Git concerne la conversion LF/CRLF du manifeste, pas Lean.
- La comparaison SHA-256 avec le début du lot constate deux ajouts Lean,
  aucune suppression, et six fichiers existants modifiés : la façade locale,
  l'import du client dans l'audit exhaustif, le manifeste, ses deux checkers
  et ce plan. Tous les autres fichiers sont identiques, dont les quatre
  fondations, le maître, la machine, les contrats acquis, les modules
  numériques, la configuration, la cible canonique et le registre.

Aucun commit, push, changement de branche ou audit indépendant n'est réalisé.
La branche reste `relativite`. Ce lot est vérifié dans la portée du contrat
post-comparaison décrite ici ; la cible relativiste finale demeure ouverte.

## 27. Comparaisons successives sur le support effectivement produit

### 27.1. Obligation fermée et cible inchangée

Le contrat de la section 26 autorisait une comparaison initiale, puis les
instructions de signal. Il ne permettait pas d'utiliser des réceptions
nouvelles pour une comparaison suivante. Ce lot ferme cette limitation
instrumentale : les comparaisons, émissions, relais, réceptions, inspections
et refus peuvent désormais s'entrelacer dans une histoire finie de longueur
arbitraire. La cible de la section 1 n'est ni modifiée ni déclarée atteinte.

Les sources sont
[RecurringInteractions.lean](../../RelationalPerimeter/Relativity/Production/RecurringInteractions.lean),
[RecurringFutures.lean](../../RelationalPerimeter/Relativity/Production/RecurringFutures.lean)
et le client public
[RecurringInteractionChecks.lean](../../Tests/Relativity/RecurringInteractionChecks.lean).

### 27.2. Constitution positive à chaque préfixe

`RecurringFormation` décrit l'histoire exacte des productions. Elle ne
suffit pas seule à autoriser une exécution. `RecurringCursor` exige également
`RecurringConstitution formation`, un témoin dans `Type` couvrant toute
cette même histoire : chaque comparaison doit avoir deux occurrences de
réception effectivement constituées dans son préfixe et distinctes.

`RecurringArrival` relie une occurrence de lecture à son signal effectivement
reçu. Il peut reprendre les témoins des histoires antérieures, être formé
par une nouvelle réception, ou être transporté à travers une production.
Une comparaison ne crée pas ce témoin pour sa propre sortie.
`recurring_comparison_not_reception` et `recurring_given_not_reception`
ferment explicitement les deux confusions : une lecture calculée et une
lecture initialement fournie ne deviennent pas des réceptions par égalité
numérique. Pour comparer une sortie nouvelle comme une réception, il faut
l'émettre puis la recevoir effectivement.

`RecurringPair.gap` consomme les deux témoins positifs en suivant leurs
réceptions. `gap_exact` raccorde ce calcul aux lectures des deux occurrences
du support courant. `RecurringComputed` fixe l'action arithmétique déclarée ;
le curseur exige en plus sa constitution admissible et l'interprétation
exacte de cette même histoire dans le support fondateur. Ni un producteur
arbitraire ni une cible numérique indépendante ne sont reçus par l'exécuteur.

`RecurringCursor.fromInstrument` conserve le curseur réellement produit
par la première comparaison, sa formation et son interprétation déjà stockée.
`recurring_embeds_actual_instrument` prouve l'égalité de leurs supports par
`rfl`. L'entrée `fromCursor` conserve de même le curseur signal existant.
Ces entrées ne reconstruisent pas un nouveau support `given` et ne rejouent
aucune action. Les anciens contrats restent inchangés : leur restriction
antérieure n'est pas silencieusement remplacée par un contrat plus large.

### 27.3. Productions partagées et continuation effective

`executeRecurring` produit une détermination positive. `performRecurring`
la forme une fois, puis `RecurringCursor.extend` construit le successeur
depuis cette détermination et les interprétations déjà conservées. Sortes
et valeurs sont des projections directes ; lire une ressource n'exige pas
d'éliminer d'abord l'ensemble des témoins de formation.

`RecurringProduces.formation`, `.constitution`, `.resourceFormation` et
`.interpretation` raccordent ces champs à la même production. La proposition
d'interprétation contrôle le raccord ; elle ne remplace pas les témoins
constitutifs positifs. `recurringProductionHistory` enregistre la tête
stockée, sans rappeler un producteur.

`performRecurringRequest` résout une seule admission courante, puis retourne
ensemble l'événement, le successeur, le statut et l'histoire. Une inspection
ou un refus ne produit aucune ressource. `runRecurringRequests` forme cette
tête avant d'exécuter la suite depuis son successeur. `.continue` repart du
curseur conservé, et `.continuedHistory` compose les histoires déjà produites.
Aucune tête ne reçoit une histoire future ou un curseur futur en paramètre.

Les projections séparées `recurringContract.next` et `.event` sont la
spécification de référence. L'exécution partagée appartient au runner,
pas à une affirmation d'évaluation unique de cette spécification générique.

### 27.4. Contrat fixé, dépendances et longueur arbitraire

`RecurringAdmission` couvre les quatre requêtes locales antérieures et
la comparaison de deux réceptions distinctes. `decideRecurringAdmission`
construit positivement l'admission ou sa réfutation. Les refus de port absent,
de mauvaise sorte, de lecture non reçue ou de répétition du même port font
partie du contrat, et non d'un prérequis implicite du client.

`recurring_all_futures_exact` prouve l'égalité du rapport exécuté et du
contrat pour toute liste finie de requêtes, comparaisons incluses. Le curseur
final est raccordé à la continuation de référence par
`recurring_final_cursor_exact`. La borne sur la longueur de l'histoire
compte les productions effectives ; ce n'est pas une borne de coût physique.

`RecurringUsed` conserve les dépendances antérieures et forme les nouvelles
dépendances depuis les ports réellement utilisés. Les comparaisons ont deux
ports de lecture ; les instructions de signal gardent leurs ports existants.
Les positions prouvent l'absence de cycle dans ces dépendances utilisées,
sans prétendre caractériser toutes les influences physiques possibles.

`recurringHistoryTransport`, `recurringHistoryArrival` et
`recurringHistoryUsed` transportent respectivement références, réceptions
et dépendances le long des productions effectives. Les lectures antérieures
et la distinction des occurrences sont conservées. En particulier,
`recurring_history_arrival_measure` prouve qu'un témoin de réception
transporté conserve sa lecture, au lieu de la recalculer par une nouvelle
exécution de son origine.

`repeatRecurringPair` utilise le même performer de requêtes. Après chaque
tête, il transporte les réceptions réellement disponibles et poursuit depuis
ce curseur. Il enregistre ses requêtes pendant cette récursion ; il ne rejoue
pas des actions pour construire au préalable une liste de curseurs futurs.
Pour tout entier `count`, ses requêtes et son histoire ont exactement cette
longueur, son rapport satisfait le même contrat et ses sources restent
distinctes. Le nombre 40 du smoke test n'est pas la portée de ces théorèmes.

### 27.5. Cas fermé et correction des preuves concrètes

Le client importe uniquement `RelationalPerimeter`. Il exécute deux émissions
et leurs réceptions, puis la première comparaison. Les deux lectures égales
donnent zéro, sans identifier les occurrences sources. Il refuse d'utiliser
directement cette sortie comme une réception et refuse le même port deux fois.

Il émet et reçoit ensuite cette sortie, relaie le signal avec la calibration
reçue, reçoit ce relais, puis compare ces deux réceptions nouvelles. La sortie
est un. Cette sortie est à son tour émise et reçue ; une troisième comparaison
donne zéro. Ces valeurs sont prouvées sur les déterminations des productions
stockées. Le client exécute aussi le contrat adressé avec actions, inspections
et refus entremêlés : huit productions effectives. Il poursuit ensuite depuis
son curseur réel et conserve les témoins des réceptions et dépendances initiales.

Les premières tentatives de preuves numériques par réduction intégrale
ont rencontré des timeouts de noyau et, dans une tentative, un dépassement
mémoire. Elles ne sont pas livrées comme preuves ou résultats de coût.
Le raccord de données a été rendu direct ; les preuves finales composent
les lois rationnelles avec l'exactitude des réceptions et transports stockés.
Elles ne relèvent pas les limites du noyau, n'utilisent aucune évaluation
native comme preuve et n'acceptent aucun trou.

Enfin, deux signaux de même lecture finale mais de parcours enregistrés
différents restent distinguables par une inspection future permise.
`recurring_futures_preserve_readout` impose cette conservation sous le
contrat fixé. Le test fermé prouve la non-équivalence future des deux états.
Le lot ne supprime donc pas une différence de parcours encore lisible.

### 27.6. Frontière scientifique maintenue

Il s'agit toujours d'une loi instrumentale locale déclarée : soustraction
de lectures effectivement reçues, avec le même mécanisme de support et de
constitution. La disponibilité simultanée de ports dans ce support ne prouve
ni leur colocation physique ni une rencontre relativiste. Aucune métrique,
vitesse limite ou équation de gravitation n'est introduite implicitement.

La répétition des comparaisons est maintenant construite. Restent notamment
le transport exact de ce contrat enrichi entre présentations, la clôture du
contrat physique final, les autorisations de regroupement qui le respectent,
la continuité intrinsèque, la géométrie, la dynamique et la reconstruction
exacte du domaine relativiste. Aucun regroupement ou oubli n'est annoncé
dans ce lot. Sous les inspections actuelles, les effets de parcours encore
observables doivent rester distinguables.

Le maître computationnel, la machine, les quatre fondations, les modules
numériques, la cible canonique et le registre scientifique ne sont pas
modifiés. Leurs revues ne sont pas déclarées closes par ce lot. Les nouveaux
modules sont classifiés `H7` et `H8`, et la façade devient `H9`, avec la même
règle d'import strictement descendant et les mêmes exclusions de strates.

### 27.7. Vérification de ce lot

Sur cette copie de travail Windows, `lake build` réussit : 288 jobs, sans
avertissement Lean. Les deux commandes complètes `bash scripts/verify.sh`
et `pwsh -NoProfile -File scripts/verify.ps1` réussissent également. Elles
vérifient 286 fichiers Lean, 233 modules de production tous classifiés et
accessibles, et les 23 fixtures d'échec attendu avec leurs diagnostics et
sites précis. Le balayage de 24 072 constantes, sur 285 modules importés,
compte zéro exception écrite à la main. Les 364 exceptions détectées sont
générées par le compilateur. Les déclarations principales de ce lot ont
chacune un audit sans axiome dans l'unique bloc final de leur fichier.

Le premier passage PowerShell a détecté une table arrêtée à H8 malgré
l'admission de H9 dans l'inventaire. La table a été étendue à H9 ; la règle
reste identique : un module local ne peut importer qu'une strate locale
strictement antérieure et les strates fondatrices ou numériques autorisées.
La vérification complète réussit après cette correction, sans ajouter de
strate libre.

Une lecture manuelle des corps C générés de `executeRecurring`,
`RecurringCursor.extend`, `performRecurring`, `recurringProductionHistory`,
`performRecurringAdmitted`, `performRecurringRequest`, `runRecurringRequests`
et `repeatRecurringPair`, ainsi que de leurs helpers de formation et de
réception, confirme le partage décrit en 27.3 sur ces chemins locaux.
Ce contrôle manuel ne devient ni un contrôleur automatique général, ni une
borne globale de coût ou une mesure physique. Les contrôleurs compilés
existants du maître et de la machine continuent à réussir ; ils ne sont pas
présentés comme un contrôleur automatique de ces nouveaux chemins.

Le scan des sources n'a trouvé aucun des termes Lean interdits. Les trois
nouveaux fichiers ont chacun exactement un bloc d'audit à leur toute fin.
Les 53 liens locaux présents dans ce plan pointent vers des fichiers
existants. `git diff --check` réussit ; les nouveaux fichiers ont été
contrôlés séparément pour les espaces de fin de ligne et de fichier.

La comparaison SHA-256 avec l'état de départ de ce lot trouve trois fichiers
ajoutés, six fichiers modifiés et aucun fichier supprimé. Les modifications
sont limitées aux deux nouveaux modules, à leur client public, à la façade
locale, à l'import du balayage global, aux deux contrôleurs de stratification,
à leur inventaire et à cette section du plan. Les autres sources et documents
de départ, notamment les fondations, le maître, la machine, les contrats
antérieurs, la cible canonique et le registre scientifique, sont inchangés.

Aucun commit, push, changement de branche ou audit indépendant n'a été
réalisé. La branche reste `relativite`. Ce lot instrumental est vérifié dans
la portée précisée ci-dessus ; la cible relativiste finale demeure ouverte.

## 28. Transport du contrat de comparaisons successives

### 28.1. Obligation traitée, sans changement de cible

Ce lot poursuit la section 27 depuis le commit
`d7402956939171f632e81027f9533f978b0ab2e6`, sur `relativite`. Il ferme le
transport du contrat instrumental enrichi entre présentations constituées,
pas la reconstruction du domaine relativiste de la section 1. Il ne change
aucune admission, loi locale ou observation du contrat `recurringContract`.

L'implémentation se trouve dans
[RecurringPresentation.lean](../../RelationalPerimeter/Relativity/Production/RecurringPresentation.lean),
[TransportedRecurringRequests.lean](../../RelationalPerimeter/Relativity/Production/TransportedRecurringRequests.lean)
et leur
[client public fermé](../../Tests/Relativity/TransportedRecurringChecks.lean).
Ces fichiers ne reconstituent pas une racine reçue sur un support produit.
Ils consomment les curseurs, déterminations et témoins de réception existants.

### 28.2. Formation et transport positif des déterminations

`RecurringRaccord` porte les références de sorte préservée et leurs deux
lois de retour, l'exactitude des lectures, puis des fonctions positives
transportant les réceptions et les dépendances utilisées dans les deux sens.
Une égalité numérique n'est donc pas suffisante pour devenir une réception.
Les vues `RecurringArrival.view` et `RecurringUsed.view` éliminent les
témoins effectivement stockés ; elles ne rappellent pas leurs producteurs.
Les équivalences propositionnelles finales sont des conséquences de ces
transports de témoins en `Type`, pas leurs substituts.

`RecurringPair.rename` transporte les deux réceptions exactes, leurs signaux
et leur distinction. `recurring_renamed_gap` conserve la lecture de leur
comparaison. Les prolongements `afterSignal` et `afterComparison` consomment
les déterminations déjà produites dans les deux présentations. Ils forment
les nouveaux transports de réception et de dépendance depuis ces témoins.
Leur projection de références est directement l'extension du transport
antérieur ; la lecture d'une adresse n'élimine pas tous les témoins de rôle.

La sortie d'une comparaison reste une lecture calculée, non une réception.
Sa sortie fraîche n'admet aucun témoin de réception. Une réception exécutée
ultérieure peut en revanche fournir un nouveau port reçu. La différence
entre ces deux formations reste visible dans les types et dans l'admission.

`independentRecurringPair` ferme le raccord initial sur deux productions
effectives des mêmes instructions indépendantes, dans les deux ordres.
`independentPairArrival` conserve le signal réellement reçu, y compris les
réceptions déjà présentes dans l'histoire antérieure. Ce raccord n'est pas
une hypothèse de compatibilité laissée ouverte dans le client.

### 28.3. Exécution partagée et preuves du contrat complet

`RecurringAdmission.rename` construit l'admission transportée ; `.returned`
la ramène au port source exact. L'unicité de l'admission est prouvée à partir
des résolveurs existants et de leurs témoins positifs. Le théorème
`recurring_transported_admission_exact` conserve toutes les admissions et
tous les refus, pour toute requête, pas seulement les requêtes admises.

`pairedRecurringRequest` résout une admission source courante. Pour une
action admise, `pairedRecurringAdmitted` effectue une production dans
chaque présentation, puis partage les déterminations pour l'événement,
l'histoire et le raccord suivant. Le runner de comparaison exécute donc
deux présentations ; il n'est pas annoncé comme un seul appel de production
au total. Aucun producteur n'est rappelé pour reconstruire le raccord ou
l'événement d'une même présentation. Inspection et refus ne produisent
aucune ressource et conservent les curseurs.

Les deux théorèmes d'exactitude de `pairedRecurringRequest` raccordent ses
réponses entières aux performers existants, y compris au résolveur propre
de la présentation cible. Le transport positif de l'admission ne remplace
donc pas le contrat cible par une interface plus facile.

`runCorrespondingRecurring` produit la tête et son raccord avant la suite,
puis poursuit depuis les deux curseurs réellement produits. Chaque requête
est traduite avec ce raccord courant. Le raccord final et les histoires
stockées permettent une nouvelle continuation sans replay. Les preuves
`correspondingRecurring_source_exact` et `correspondingRecurring_target_exact`
raccordent les exécutions entières aux deux runners antérieurs.
`recurring_transported_all_futures` conserve le rapport complet du contrat
sur toute liste finie de requêtes, de longueur arbitraire, dans les deux
directions du raccord. Les comptes de productions et de requêtes sont
raccordés séparément ; ils ne sont pas des bornes de coût ou de durée.

Les helpers `firstContinuedHistory` et `secondContinuedHistory` reçoivent
la continuation déjà exécutée, et composent uniquement ses histoires
stockées avec celles du préfixe. Leur première version recevait une liste
de requêtes et relançait `.continue` : la lecture du C a révélé ce défaut,
corrigé avant la validation finale. `recurring_continued_history_uses_cached_suffix`
raccorde les deux assemblages à ces mêmes histoires conservées.

### 28.4. Cas fermé et distinction entre preuve et smoke test

Le client importe uniquement `RelationalPerimeter`. Il échange un relais
et une réception qui utilisent tous deux l'ancien signal, sans que la
seconde instruction reçoive le nouveau résultat de la première. Les deux
présentations ont donc des ordres et des adresses différents sur des
occurrences réellement constituées.

Le cas prouvé entrelace une inspection, une nouvelle réception, une
comparaison et deux refus. Il conserve le rapport, transporte les requêtes
avec les adresses courantes, produit deux nouvelles ressources par
présentation et calcule un écart un. Les réceptions et dépendances initiales
sont transportées jusqu'aux curseurs finaux puis ramenées positivement.
Le client poursuit depuis ces curseurs. Des contrôles séparés refusent le
même port deux fois et une lecture initiale non reçue, même à valeur égale.

Un contre-exemple fermé montre qu'une traduction figée à la permutation
initiale ne conserve pas ce contrat : après une réception, elle désigne
un signal au lieu du port de lecture attendu et sa comparaison est refusée.
Le transport courant admet la comparaison correspondante.

Le smoke test plus long exécute treize requêtes, cinq productions dans
chaque présentation, et observe deux comparaisons, de valeurs un puis zéro.
Il est identifié comme une vérification d'exécutabilité, non comme une
preuve par évaluation native, une mesure physique ou un résultat expérimental
confirmatoire. L'exactitude de toute longueur vient des théorèmes généraux.

Les premières réductions intégrales du tableau long ont dépassé le budget
par défaut du noyau. Le cas numérique prouvé a été réduit, tandis que la
séquence longue reste exécutée et que la portée générale reste inchangée.
Aucune limite de preuve n'a été relevée et aucun trou n'est conservé.
Deux helpers initiaux dépendaient d'un lemme du compilateur non admissible :
leurs définitions ont été remplacées par des cas constructeurs exhaustifs
et un codage numérique de test. Leurs audits finaux doivent être sans axiome,
comme ceux de toutes les déclarations écrites de ce lot.

### 28.5. Stratification, préservation et suite du plan

Les nouveaux modules sont `H8` et `H9` ; la façade locale devient `H10`.
Les contrôleurs Bash et PowerShell gardent la même règle strictement
descendante et les mêmes exclusions, avec H10 explicitement classifié.
Aucun niveau libre n'est ajouté. Le maître, la machine, les quatre
fondations, les modules numériques et instrumentaux antérieurs, les cibles
canoniques et le registre scientifique restent inchangés.

Le transport instrumental ouvert en 27.6 est maintenant construit. Restent
le contrat physique final, les autorisations de regroupement compatibles
avec ses effets, la continuité intrinsèque, la géométrie, la dynamique et
la reconstruction exacte du domaine relativiste. Le transport de
présentation ne devient ni un regroupement des événements, ni un oubli de
parcours, ni une preuve de colocation ou de gravitation.

### 28.6. Vérifications sur les sources finales du lot

`bash scripts/verify.sh` et `pwsh -NoProfile -File scripts/verify.ps1`
réussissent tous deux, le second sous Windows natif. Leur construction
complète réussit sur 291 jobs, sans erreur ni avertissement Lean. Les deux
scripts contrôlent les mêmes 289 fichiers Lean, 235 modules de production
classifiés et accessibles sans orphelin, et 23 fixtures de rejet avec leurs
diagnostics attendus.

Le balayage global contrôle 24 533 constantes dans 288 modules : les 364
exceptions sont générées par le compilateur, aucune déclaration écrite
dans les sources ne dépend d'un axiome. Les déclarations de ce lot ont
toutes un audit sans axiome. Les scans des termes interdits et des blocs
d'audit réussissent. Les contrôleurs compilés existants du maître, des
agents et de la machine intégrée réussissent également.

La lecture manuelle des corps C générés des nouveaux runners, transports
et assemblages confirme le partage sur les chemins nommés en 28.3. En
particulier, les deux assemblages d'histoire prolongée appellent uniquement
la composition des histoires stockées, sans relancer la continuation.
Ce contrôle local n'est ni une couverture automatique générale du nouveau
code compilé, ni une borne de coût physique.

`git diff --check` réussit ; les trois nouveaux fichiers sont aussi
contrôlés séparément pour leurs espaces et leurs blocs d'audit finaux.
Les 56 liens locaux du plan sont valides. Le registre scientifique passe
ses contrôles statiques sans modification de ses statuts ouverts.

La comparaison SHA-256 avec le départ du lot relève trois fichiers ajoutés,
six modifiés et aucun supprimé. Les changements restent limités aux deux
modules, au client, à la façade, à l'import du balayage global, à l'inventaire
de stratification, à ses deux contrôleurs et à ce plan. Les autres sources
et documents, notamment les fondations, le maître, la machine, les contrats
antérieurs, les cibles canoniques et le registre, sont inchangés.

Aucun commit, push, changement de branche ou audit indépendant n'est
effectué pour ce lot. La branche reste `relativite`, à partir de `d740295`.
Ces vérifications ferment la portée instrumentale de la section 28 ; elles
ne déclarent pas atteinte la cible physique finale.

## 29. Recherche locale d'un échange et continuation regroupée

### 29.1. Obligation et critères fixés avant l'implémentation

Ce lot part de `fc58a178da0cd35261120a0589cb26c438349775`. La demande de
poursuite autorise l'implémentation locale, sans commit, push ou audit externe.
La cible finale et les contrats existants restent inchangés.

Le premier chercheur reconnaîtra une classe précise de relations : l'échange
de deux productions dont la seconde utilise uniquement les ressources
antérieures à la première. Il inspectera les ports réellement utilisés,
retournera leur instruction d'origine ou un port frais positivement utilisé.
Un refus signifie l'impossibilité de cet échange de ports anciens ; il ne
signifie pas l'inexistence de toute autre relation de regroupement.

La relation trouvée devra agir sur les déterminations stockées : changer la
présentation de ces productions, conserver leurs sorties, réceptions et
dépendances, sans rappeler leurs producteurs. Les deux retours de références
et l'accord de toutes les suites du contrat récurrent autoriseront ensuite
une continuation commune. Cet échange de présentation ne sera pas appelé
une nouvelle interaction physique.

Le runner regroupé devra produire une seule détermination par demande
productive, puis transporter cette même détermination dans l'autre
présentation. Il ne devra pas appeler le producteur une seconde fois pour
fabriquer sa preuve d'accord. Les admissions, refus, événements, successeurs,
histoires et demandes traduites seront raccordés aux runners existants.
La reprise partira des sorties conservées ; l'assemblage consommera un
suffixe déjà exécuté. Aucun avenir achevé ne sera une entrée du chercheur.

Le client fermé devra comporter un échange trouvé, un échange refusé parce
que la seconde production consomme la sortie fraîche, et une lecture future
qui distingue ce cas dépendant d'un échange naïf. Il devra aussi conserver
les occurrences sources distinctes et poursuivre des comparaisons admises
avec les adresses courantes. Les preuves générales porteront sur toutes
les listes finies, pas seulement sur ce client.

La validation comprend les deux gates complètes, l'audit axiomatique, les
liens et le diff, ainsi qu'une lecture des corps C des nouveaux chemins de
recherche, transport et continuation. Ce lot ne ferme pas le contrat physique
final, la minimalité mémoire, la continuité ou la reconstruction relativiste.

### 29.2. Relation reconstruite depuis les rôles effectivement produits

Le module [DiscoveredExchange](../../RelationalPerimeter/Relativity/Production/DiscoveredExchange.lean)
reçoit un `StoredPairProduction`. Sa seconde instruction peut consommer la
sortie fraîche de la première ; l'indépendance n'est donc pas une hypothèse
de ce préfixe reçu. Les deux déterminations sont positives et leurs indices
imposent le contexte effectivement produit par la première.

`searchStoredExchange` lit `recordedInstruction` sur le rôle stocké de la
seconde production. Le chercheur `findOldInstruction` inspecte ses ports,
sans lire une continuation ni comparer seulement leurs valeurs. Il retourne
soit l'instruction sur les ressources anciennes avec son égalité de renommage,
soit un `InputPort` frais réellement utilisé. `recordedInstruction_exact`
relie cette instruction lue à l'indice de la production reçue.

`exchange_found_iff_old` caractérise exactement la portée de ce chercheur :
l'échange est trouvé si et seulement si cette instruction peut être ramenée
aux seuls ports anciens. `exchange_refusal_excludes_old` interdit alors ce
même témoin dans le cas refusé. Il ne conclut pas que deux calculs utilisant
une ressource fraîche ne pourraient jamais être reliés autrement.

Les sélecteurs `discoveredExchangeOfFound` et `freshPortOfRefusedExchange`
retournent les données de cette recherche exécutée, pas une hypothèse de
relation. `freshUsedEdge` raccorde le port refusant l'échange à une dépendance
positive entre les deux occurrences effectivement produites.

### 29.3. Action sur les déterminations et préservation séparée

`exchangeStored` consomme les deux déterminations existantes. `returnOld`
ramène le rôle indépendant de la seconde aux ports anciens ; `weaken`
transporte celui de la première sous la seconde devenue première. Les
sorties sont les projections des déterminations reçues, dans l'ordre inversé.
`exchanged_outputs_are_cached` donne leurs deux égalités exactes.

`realizeStoredExchange` consomme le résultat positif du chercheur et produit
l'exécution échangée ainsi que son `AddressedRecurringRaccord`. Ce dernier
reprend les transports réversibles déjà construits : références courantes,
réceptions positives, dépendances utilisées et valeurs lues. Il ne remplace
pas les occurrences par leurs valeurs égales.

La préservation de toutes les suites du contrat récurrent est ensuite
prouvée par `discovered_exchange_all_futures`. Elle n'est pas une simple
égalité de la dernière lecture ni la définition d'un marqueur singleton.
Il s'agit d'une relation entre présentations et d'une autorisation de partager
leur continuation, pas d'une identification des événements ni d'une nouvelle
loi physique de rencontre.

### 29.4. Une production partagée, puis une continuation effective

Le module [GroupedRecurringContinuation](../../RelationalPerimeter/Relativity/Production/GroupedRecurringContinuation.lean)
construit `sharedRecurringAdmitted`. Chaque branche productive appelle une
fois `performRecurring` sur la source. `transportRecurringDetermination`
transporte le rôle positif avec le raccord reçu et garde la même sortie
stockée. Le successeur de l'autre présentation est formé avec cette
détermination transportée, sans appeler son producteur.

`shared_request_exact` et `shared_run_exact` raccordent ces données entières
aux exécuteurs antérieurs, qui restent inchangés. `shared_recurring_runners_exact`
raccorde les deux exécutions entières aux runners de référence.
`shared_recurring_all_futures` porte sur toutes les listes finies, de longueur
arbitraire, du contrat existant : admissions, refus, inspections, émissions,
relais, réceptions et comparaisons entre réceptions effectivement constituées.
Le sens inverse utilise le raccord inverse, sans autre hypothèse de valeur.

`runSharedRecurring` produit sa tête avant sa queue. La queue reçoit les
curseurs et le raccord réellement produits par cette tête. La traduction de
chaque demande utilise ses adresses courantes, pas la permutation initiale.
`continueShared` reprend ces mêmes curseurs finaux. Les assemblages d'histoire
existants reçoivent le suffixe déjà exécuté, sans relancer sa continuation.

`searchExchangeAndContinue` relie explicitement les deux passages : il
exécute une recherche, puis consomme son résultat. En cas de succès, la
continuation partagée utilise le raccord trouvé. En cas de refus, l'exécution
source se poursuit et le port frais demeure disponible comme témoin du refus.
`search_continuation_source_exact` conserve le runner source dans les deux cas.

### 29.5. Client fermé, refus réel et séparateur futur

Le client [DiscoveredGroupingChecks](../../Tests/Relativity/DiscoveredGroupingChecks.lean)
importe uniquement l'API publique. Dans le cas accepté, un relais puis une
réception utilisent l'ancien signal. Le chercheur trouve l'échange ; ses
sorties réemploient les déterminations produites. Les deux premières adresses
sont échangées, non identifiées. Les occurrences sources restent distinctes
après les prolongements.

Le client entrelace une inspection, une réception, une comparaison et deux
refus. Les autorisations valent exactement `[true, true, true, false, false]`.
Les deux rapports sont égaux, les demandes traduites emploient les adresses
courantes, et une nouvelle continuation reprend les curseurs produits.
Les réceptions se transportent positivement jusqu'à ces curseurs et reviennent.
Les théorèmes génériques, et non la longueur de ce client, établissent
l'accord sur toute suite finie dans les deux directions.

Dans le cas refusé, la même première détermination est conservée mais la
seconde réception consomme le signal fraîchement relayé. La recherche retourne
son port utilisé et la dépendance effective correspondante. Un échange naïf
recevrait au contraire l'ancien signal : une inspection future donne zéro
au lieu d'un. `future_report_separates_naive_exchange` prouve la différence
des rapports du contrat, pas seulement celle de deux valeurs internes.

### 29.6. Contrôle de calculabilité et partage du code compilé

La première version du transport de comparaison éliminait directement le
témoin `RecurringComputed` dans une définition de données. Le C généré
recalculait alors `recurringDifference` dans l'autre présentation, malgré
l'égalité prouvée de la sortie extérieure. Ce défaut a été corrigé avant la
validation finale : `RecurringComputed.output_exact` conserve l'égalité
dans la preuve, et le transport de données garde opaque la sortie reçue.
Le corps C final stocke cette même sortie dans le rôle transporté sans
recalculer la différence.

La lecture des corps C complets vérifie les quatre branches productives de
`sharedRecurringAdmitted` : chacune appelle un producteur, puis transporte
ce même résultat et assemble les deux réponses stockées. L'inspection et
le refus n'appellent aucun producteur. La lecture vérifie aussi les
successeurs, les assemblages, la recherche unique et l'ordre tête puis queue.

Le graphe des appels directs des chemins de recherche, d'échange stocké,
de transport du rôle et de la production, et d'assemblage ne rappelle aucun
producteur. Les fonctions d'opération conservées dans les formations restent
des capacités stockées ; leur allocation n'est pas assimilée à leur appel.
Les fermetures de traduction et de transport ont été lues séparément.
Ce contrôle local du C ne constitue ni une gate automatique exhaustive du
nouveau runtime ni une borne de coût, de mémoire ou de durée physique.

### 29.7. Vérifications, préservation et obligations restantes

Sur les sources finales de ce lot, `bash scripts/verify.sh` et
`pwsh -NoProfile -File scripts/verify.ps1` réussissent ; PowerShell est exécuté
sous Windows natif. Le build complet comporte 294 jobs, sans erreur ni
avertissement Lean. Les gates sélectionnent les mêmes 292 fichiers Lean et
contrôlent 237 modules de production classifiés, accessibles et sans orphelin,
ainsi que les 23 fixtures de rejet existantes.

Le balayage global contrôle 24 788 constantes dans 291 modules, avec 364
exceptions générées par le compilateur et aucune déclaration écrite dépendant
d'un axiome. Les audits de toutes les déclarations ajoutées sont sans axiome.
Les blocs finaux, les scans des termes interdits, les liens du registre et
les contrôleurs compilés existants du maître, des agents et de la machine
intégrée réussissent. Les statuts ouverts du registre ne sont pas modifiés.

Le nouveau chercheur est classifié `H9`, sa continuation partagée `H10` et
la façade locale `H11`. Les deux contrôleurs imposent encore des dépendances
strictement descendantes, sans nouveau niveau libre. La comparaison SHA-256
avec le départ du lot relève trois fichiers ajoutés, six modifiés et aucun
supprimé : les deux modules, le client, la façade, l'import du balayage global,
l'inventaire, ses deux contrôleurs et ce plan. Toutes les autres sources et
documents sont inchangés, notamment les quatre fondations, le maître, la
machine, les contrats antérieurs, les cibles canoniques et le registre.

Cette section ferme la recherche locale d'un échange et son utilisation par
une continuation productive partagée sous le contrat récurrent existant.
Les deux présentations et leurs histoires restent représentées : aucune
réduction mémoire minimale n'est revendiquée. La recherche d'autres relations,
le contrat physique final, les regroupements exacts sous ce contrat, la
continuité, la géométrie, la dynamique et la reconstruction relativiste
restent des obligations du plan. La cible finale de la section 1 est inchangée.
Aucun commit, push, changement de branche ou audit externe n'est effectué.

## 30. Descriptions attachées et raffinements des lecteurs

### 30.1. Obligation fixée avant l'implémentation

Le départ est `57db7ff72f54f53508aacd9d35aebe1eae20bfc6`, sur `relativite`.
Ce lot poursuit les constructeurs descriptifs de R2-R3 ; il ne ferme pas le
contrat physique final ni la reconstruction du domaine relativiste.

Une description doit suivre une occurrence du support effectivement constitué.
Sa grammaire partira de ce support, incorporera les productions déjà stockées
et consommera les transports exacts autorisés. Ses références conserveront
leur sorte, leurs valeurs, leurs réceptions et leurs dépendances utilisées.
Le raccord trouvé par la recherche sera utilisé par un consommateur concret,
y compris après la continuation partagée du lot 29. Aucun producteur ne sera
rappelé pour former ces descriptions.

Pour les signaux, trois lecteurs complémentaires porteront sur le payload,
la lecture rationnelle et la liste des incréments effectivement enregistrés.
Le raffinement décrit ici ajoute des lecteurs de ce contrat existant ; il
ne prétend pas affiner une précision numérique ou produire une mesure nouvelle.
La restriction d'une description plus riche devra fonctionner sur cette
description seule, sans relire le support. Un raffinement commun sera construit,
avec ses deux restrictions. Les lecteurs conjoints retrouveront exactement
le record, sans retrouver ni identifier par là l'occurrence source.

Le prolongement physique et le changement de lecteurs auront des opérations
et indices distincts. Les preuves raccorderont restriction, transport et
prolongement, sur toute longueur finie. Les descriptions après continuation
consommeront les sorties et histoires reçues, pas des suffixes réexécutés.

Un client public fermé montrera un échange découvert, sa continuation et
ses descriptions raffinées. Un autre construira deux parcours ayant les mêmes
payload et lecture finale, mais des listes d'incréments différentes ; une
inspection future du contrat récurrent devra les distinguer. L'accord de
lecteurs partiels ne sera jamais exporté comme autorisation d'oubli.

Les deux gates, l'audit global et les contrôles du code compilé devront passer.
Fondations, maître, machine, contrats et cibles antérieurs resteront inchangés.
Cette demande n'autorise ni commit, ni push, ni audit externe.

### 30.2. Grammaire de description sur le support constitué

[ConstitutedDescriptions](../../RelationalPerimeter/Relativity/Production/ConstitutedDescriptions.lean)
définit `DescriptionPath origin current`. Ses constructeurs sont la racine
sur un curseur constitué, l'incorporation d'un `RecurringProduction` stocké,
et le changement de présentation par `AddressedRecurringRaccord`. Les deux
curseurs portent leurs formations et constitutions positives ; les références
des occurrences ne sont jamais reconstruites depuis des valeurs numériques.

`reference` compose les transports réellement reçus. `reads` conserve la
valeur de l'occurrence ancienne et `injective` conserve ses distinctions.
`arrival` et `used` transportent positivement les réceptions et les dépendances,
pas seulement leurs valeurs. Le retour d'un changement de présentation retrouve
la référence source. Il ne donne pas un inverse à une extension physique.

`prolong` élimine une histoire déjà produite pour incorporer ses déterminations.
`append` compose deux chemins descriptifs raccordés. Leurs lois de références
et `prolong_count` portent sur toute histoire finie de longueur arbitraire.
`producedCount` compte les incorporations de productions, pas le temps physique
ni le coût d'évaluation. Un changement de présentation n'augmente pas cet indice.
Ces descriptions peuvent être formées après les productions qu'elles décrivent ;
elles ne prétendent pas refaire ni remplacer leur exécution stagewise.

### 30.3. Lecteurs complémentaires et raffinement commun

`SignalReaders` sélectionne les trois composantes d'un `SignalRecord` déjà
produit : payload, lecture rationnelle et liste des incréments. `describeSignal`
consomme un chemin et la référence de l'occurrence source, transporte cette
référence puis lit son record conservé. `described_signal_exact` raccorde
cette lecture à celle de l'origine constituée. Aucun record libre ne remplace
ce record dans le constructeur descriptif.

`ReaderRefinement` exprime l'inclusion des lecteurs. `SignalObservation.restrict`
fonctionne sur l'observation reçue seule, sans chemin, support ou producteur.
`restrict_signal_exact` et `signal_restriction_compose` prouvent ses lois.
`SignalReaders.join` construit un raffinement commun et
`described_signal_common_refinement` donne ses deux restrictions exactes.
`joint_signal_readers_exact` caractérise l'accord des lecteurs complets par
l'égalité du record, jamais par l'identité de ses occurrences sources.

`described_signal_prolong` et `described_signal_reexpress` conservent ces
descriptions lors des passages autorisés. La restriction retrouve donc les
lectures moins riches avant ou après transport et prolongement. Il s'agit
de lecteurs supplémentaires du cache déjà accessible dans le contrat récurrent,
pas de précision analytique nouvelle, d'une nouvelle sonde physique ou d'une
autorisation de supprimer de la mémoire les champs non affichés.

### 30.4. Consommation de la continuation et cas fermés

`continuedExchangeDescription` reçoit l'échange trouvé et un résultat de
continuation raccordé à ses deux présentations. Il incorpore l'histoire source
stockée, puis le raccord des curseurs finaux effectivement reçus. L'échange
fixe les indices des présentations ; à ce stade, le consommateur utilise les
données de la continuation, sans relire la recherche ni rappeler le runner.
`continued_exchange_description_exact` conserve le record de l'occurrence
source à travers ce passage.

Le client [ConstitutedDescriptionChecks](../../Tests/Relativity/ConstitutedDescriptionChecks.lean)
importe uniquement l'API publique. Il construit un relais et une réception
sur un ancien signal, trouve leur échange et poursuit par réception,
comparaison puis refus. Les deux productions de cette continuation sont
incorporées dans la description ; le raffinement de lecteurs n'en ajoute
aucune. Les réceptions et dépendances anciennes sont transportées positivement.
Les deux signaux sources restent distincts. Les lois génériques conservent
le record sur toute suite finie, pas seulement sur ce client.

Un second cas construit deux relais d'incrément un et un relais d'incrément
deux, avec les calibrations reçues déclarées. Payload et lecture finale sont
identiques ; les listes d'incréments ont des longueurs différentes.
`differing_paths_separate_inspection` construit le séparateur : l'inspection
du signal à son adresse courante. `actual_future_reports_differ` le raccorde
aux deux rapports réellement exécutés. L'accord partiel n'autorise donc pas
l'oubli sous ce même contrat, sans supposer de géométrie ou d'effet de courbure.

### 30.5. Calculabilité et frontière de portée

La lecture des corps C des constructeurs descriptifs, de leurs restrictions
et de leurs consommateurs confirme la réutilisation des curseurs,
déterminations et raccords reçus. `prolong` assemble des nœuds depuis les
déterminations stockées ; `describeSignal` transporte une référence et lit
les valeurs du curseur ; `restrict` ne reçoit que l'observation et les lecteurs.
Le graphe local des appels directs et des fermetures statiques comprend
31 racines et 46 fonctions de production accessibles, sans appel à un
producteur, au chercheur ou au calcul de différence des comparaisons.

Les helpers externes sont les transports de support identité/composition
et la lecture d'une ressource stockée. Les callbacks du raccord concret sont
ceux de l'échange et de la continuation partagée du lot 29. Ce contrôle local
ne prouve ni un coût total, ni une minimalité mémoire, ni l'absence de travail
dans tous les callbacks qu'un utilisateur pourrait fournir à l'interface
générique de transport.

Ce lot ferme la grammaire descriptive attachée, les restrictions et le
raffinement commun de ces lecteurs du record. Il ne ferme pas `LocationAgreement`,
une précision numérique raffinable, une rencontre physique, le contrat physique
final, un quotient de mémoire, le continuum, la géométrie ou la dynamique.
L'accord de valeurs ne devient pas un accord de localisation. La cible finale
de la section 1 reste inchangée.

### 30.6. Vérification complète et préservation

Les deux commandes `bash scripts/verify.sh` et
`pwsh -NoProfile -File scripts/verify.ps1` réussissent sur cet état, la seconde
sous Windows natif. Le build complet compte 296 jobs, sans avertissement Lean.
Les gates contrôlent les mêmes 294 fichiers Lean, les blocs d'audit finaux,
la constructivité, les frontières d'import et de migration, les contrôles
documentaires et les contrôles existants de partage du code compilé.
Les 238 modules de production inventoriés sont accessibles et stratifiés,
sans orphelin ; les 23 fixtures de rejet échouent aux sites attendus.

Le contrôle exhaustif porte sur 24 957 constantes de 293 modules. Les
364 exceptions sont générées par le compilateur ; aucune déclaration écrite
à la main ne dépend d'un axiome. Les sources nouvelles ne contiennent aucun
terme interdit et ont chacune un unique bloc d'audit à leur fin.

Le lot ajoute deux fichiers et en modifie six, sans suppression. Les
empreintes des 382 autres fichiers présents avant l'implémentation sont
identiques, notamment celles des quatre fondations, du maître, de la machine,
des contrats antérieurs, des cibles canoniques et du registre scientifique.
Les 61 liens locaux du plan sont valides et `git diff --check` est propre.

Cette vérification clôt ce lot descriptif, pas le plan relativiste complet.
Les obligations physiques énumérées en section 30.5 restent ouvertes.
Aucun commit, push, changement de branche ou audit externe n'est effectué.

## 31. Attachements à une interaction produite et effets conservés

### 31.1. Obligation fixée avant l'implémentation

Le départ est `1f8e67681512159f60bdc379f729357b63e9f0a9`, sur `relativite`.
Ce lot poursuit le raccord constitutif A1/R3. Le candidat instrumental actuel
ne comporte pas de loi de propagation ou d'admission de colocalisation ;
il serait faux de renommer sa comparaison en rencontre physique.
La cible finale reste celle de la section 1, non une simple comparaison.

Le passage disponible doit être fermé avant cette interprétation physique :
les deux arrivées participantes seront attachées à l'occurrence fraîche
d'une même comparaison effectivement produite. Leurs références et leurs
effets viendront du support et des rôles de cette production, pas d'un point,
d'un identifiant ou d'une valeur de comparaison fournis indépendamment.
Le transport suivra le chemin descriptif déjà construit. L'ancrage commun
ne devra identifier ni les réceptions ni les signaux sources et n'autorisera
aucun oubli sous le contrat récurrent complet.

Construire les témoins positifs de réception et d'utilisation des ports,
les lois de lecture et de persistance pour tous les suffixes finis, et un
runner qui partage la tête avant de poursuivre depuis son successeur réel.
Une seconde comparaison pourra produire la même valeur tout en constituant
une nouvelle occurrence ; cette différence devra être prouvée.

Le client fermé devra joindre, dans le même support et la même interaction,
deux signaux aux mêmes payload et lecture finale mais aux effets de parcours
différents. Les inspections réellement permises devront révéler la différence.
Les deux gates, l'audit exhaustif et la vérification du partage compilé devront
réussir. Aucun contrat ancien, fondation, maître, machine ou cible canonique
ne sera modifié. Aucun commit, push ou audit extérieur n'est autorisé ici.

### 31.2. Ancrage issu de la production et participants positifs

Le module [InteractionAttachments](../../RelationalPerimeter/Relativity/Production/InteractionAttachments.lean)
consomme une `RecurringProduction source (.compare pair)` déjà construite.
`comparisonAnchor` désigne son occurrence fraîche ; `comparisonExtension`
est le transport de son histoire réelle. L'égalité de sortie vient de
`head.determination.2.output_exact`, pas d'un résultat numérique extérieur.
`comparison_anchor_fresh` distingue cet ancrage de toute lecture source.

`InteractionAttachment` relie une réception source et son signal à cette
tête précise, par un témoin positif d'arrivée, un port de la comparaison
et un `DescriptionPath` depuis son successeur. `transportedArrival` et
`usedPort` transportent ces témoins dans la présentation courante.
Le record des effets est lu à la référence signal transportée dans le
curseur courant. `attached_effects_exact` raccorde cette lecture au record
source, tandis que `attached_anchor_output` lit la sortie réellement produite.

Les deux ports d'une même tête partagent l'ancrage mais restent des réceptions
distinctes (`participants_remain_distinct`). La distinction des signaux est
également conservée lorsqu'elle existe en amont ; deux réceptions distinctes
n'impliquent pas à elles seules deux signaux distincts. La lecture de l'ancrage
commun ne remplace donc aucune de ces distinctions constituées.

### 31.3. Continuation partagée et changements de présentation

`runAttachedComparison` produit une tête une fois, puis appelle le runner
récurrent depuis son successeur réel. `attached_head_independent` établit
que la tête entière ne dépend pas de la liste des demandes futures.
Les descriptions `first` et `second` utilisent ensuite l'histoire stockée
de la continuation ; elles ne produisent pas rétroactivement la tête.

`attached_continuation_exact` conserve tous les rapports des suffixes finis
du contrat récurrent existant, y compris les refus. La loi
`cached_comparison_event_exact` raccorde séparément l'événement de tête à
la demande de comparaison admise. Ces deux lois ne sont pas présentées
comme une égalité complète du nouvel objet avec le runner du préfixe
comparaison suivi du suffixe : cette égalité n'est pas ajoutée dans ce lot.

`prolong` suit l'histoire stockée et `reexpress` suit un raccord adressé
effectif. Leurs lois conservent les records et transportent l'ancrage ;
le retour par le raccord inverse restitue la référence de cet ancrage.
Ces opérations ne suppriment aucune ressource du contrat.

### 31.4. Cas fermé et distinctions encore révélables

Le client [InteractionAttachmentChecks](../../Tests/Relativity/InteractionAttachmentChecks.lean)
importe uniquement `RelationalPerimeter`. Il construit dans une même histoire
deux réceptions : le premier signal a subi deux relais d'incrément un ; le
second est une réémission depuis la première réception. Les payloads et les
lectures finales sont égaux, mais les records portent respectivement
`[one, one]` et `[]`. La comparaison admise produit la sortie zéro.

Les deux participants ont un même ancrage d'interaction, des références de
réception et de signal démontrées distinctes, et des témoins positifs de
réception et d'utilisation de ports. Les inspections effectivement exécutées
aux deux références révèlent les records différents. Ce séparateur compare
deux requêtes permises dans un même état ; ce n'est pas une caractérisation
nouvelle de l'équivalence future entre deux états arbitraires.

Pour toute liste finie de demandes ultérieures, le client conserve la tête,
les deux records, l'ancrage commun et la distinction des réceptions.
Une seconde comparaison des arrivées transportées produit la même valeur
numérique mais une occurrence fraîche distincte. L'ancienne interaction
reste transportée : égalité des résultats ne signifie pas identité des
interactions.

### 31.5. Vérifications et portée exacte du lot

`lake build +RelationalPerimeter` réussit avec 240 jobs. Les deux gates
`bash scripts/verify.sh` et `pwsh -NoProfile -File scripts/verify.ps1`
réussissent, la seconde sous Windows natif. Le build complet compte
298 jobs sans avertissement Lean. Les mêmes 296 fichiers Lean sont vérifiés,
les 239 modules de production sont accessibles et strictement stratifiés,
et les 23 fixtures existantes sont rejetées aux sites attendus.

L'audit exhaustif porte sur 25 086 constantes de 295 modules : 364 exceptions
générées par le compilateur, aucune déclaration écrite à la main dépendante
d'un axiome. Les deux nouveaux fichiers ont chacun leur unique bloc d'audit
final. Le module est placé en H12, au-dessus des descriptions H11 et sous la
façade H13 ; les deux contrôleurs gardent l'exigence de dépendance descendante.

Le contrôle local du C généré réemploie les parseurs de corps et de fermetures
statiques de `check-unified-codegen.py`. Il confirme un appel de
`performRecurring`, un appel de `runRecurringRequests` et le passage du
successeur de cette même tête au runner. Les constructeurs, transports et
lectures des attachements couvrent 52 racines compilées et 79 fonctions
accessibles, sans appel à ces producteurs, au runner de demandes ou au calcul
de différence. Ce contrôle est une inspection locale complémentaire,
pas une nouvelle gate permanente ; il ne borne ni les callbacks arbitraires
d'un raccord fourni, ni le coût total, ni la mémoire physique.

Le lot ajoute deux fichiers et en modifie six, sans suppression. Les
empreintes des 384 autres fichiers du départ sont identiques, notamment
celles des fondations, du maître, de la machine, des anciens contrats,
des cibles canoniques et du registre scientifique.

Cette réalisation ferme l'attachement constitutif à une interaction produite
et le maintien des effets séparément lisibles. Elle ne ferme pas la loi
physique de rencontre de A1, `LocationAgreement`, le contrat physique complet
de A4, une réduction mémoire, le continuum, la métrique ou la dynamique.
Une admission physique de rencontre devra être construite depuis les lois
primitives et les parcours, sans être déduite de la seule comparaison ou
coexistence des réceptions. La cible finale de la section 1 reste inchangée.
Aucun commit, push, changement de branche ou audit extérieur n'est effectué.

## 32. Accords des descriptions attachées et conservation des lecteurs

### 32.1. Obligation fixée avant l'implémentation

Ce lot poursuit R3.2 sur l'état local de la section 31, sans remplacer la
cible finale. Un accord sur l'interaction produite et un accord sur la
description riche des participants seront deux objets distincts.
Les deux consommeront un raccord exact des présentations constituées ;
le premier raccordera l'ancrage, le second raccordera aussi la réception
et le signal. Ni une égalité de lectures ni un code numérique libre ne
servira à fabriquer ces accords.

Construire identité, composition et retour des raccords adressés, puis
ces opérations pour les accords attachés à une même tête constituée.
Raccorder les observations de leurs effets aux lecteurs déjà définis,
avec restriction, raffinement commun et persistance sous prolongement
et changement exact de présentation. L'accord limité à l'interaction
n'autorisera pas l'oubli d'effets encore révélables au contrat complet.

Le client fermé devra utiliser un échange effectivement trouvé, puis le
transport d'une tête de comparaison déjà produite, sans la rejouer.
Il distinguera le partage de cette interaction du partage de tous les
effets attachés, et vérifiera les lois sur les références transportées.
La portée restera instrumentale : ces accords ne seront pas renommés
`LocationAgreement` et ne fermeront pas une admission physique de rencontre.

Conserver les sources du lot 31, les fondations, le maître, la machine et
les contrats précédents. Intégrer l'ajout dans l'API et la stratification,
exécuter les deux gates et contrôler les corps compilés des constructeurs.
Aucun commit, push, changement de branche ou audit externe n'est autorisé.

### 32.2. Deux accords sur une même interaction constituée

Le module [InteractionDescriptionAgreement](../../RelationalPerimeter/Relativity/Production/InteractionDescriptionAgreement.lean)
consomme les attachements du lot 31. Les deux descriptions sont indexées par
la même tête effectivement produite ; l'accord n'invente pas cette origine.
`InteractionSiteAgreement` raccorde uniquement la référence de l'ancrage de
l'interaction. `AttachedDescriptionAgreement` raccorde en plus la réception
participante et son signal. Chaque objet contient un raccord exact entre les
présentations, et non une égalité de nombres fournie pour remplacer ce raccord.
Ces types ne sont pas des accords de localisation physique.

`AddressedRecurringRaccord.identity` et `.compose` conservent les transports
aller/retour des références, des adresses et des témoins positifs d'arrivée
et d'utilisation. Les deux accords disposent d'identité, composition et
inverse. L'associativité ajoutée est une égalité point par point des références
transportées ; elle n'est pas présentée comme une égalité de tous les objets
fonctionnels. `attached_rich_return_reference` restitue chaque référence après
l'aller et le retour.

Les dépendances de lecture restent explicites : `attached_agreement_effects`
consomme le raccord exact du signal et la conservation de sa lecture ; la
réception et l'ancrage ont leurs lois séparées. Un accord riche donne un accord
d'ancrage, mais l'accord d'ancrage ne donne pas un accord riche. Deux records
différents réfutent tout accord riche, sans nier leur interaction commune.

### 32.3. Lecteurs, changements de présentation et demandes futures

`InteractionAttachment.observe` lit le record attaché avec les lecteurs
déclarés. La restriction et le raffinement commun retrouvent les lectures
partielles depuis leurs observations ; ils ne produisent pas de nouvel
événement. Le prolongement suit une histoire réellement constituée et conserve
les anciennes lectures. Le changement de présentation suit son raccord exact.
Ces opérations ne suppriment aucune ressource et ne changent aucun contrat.

`attached_joint_observations_exact` caractérise l'égalité des records par
l'accord de tous leurs lecteurs. Il ne caractérise ni l'identité des réceptions,
ni l'identité des descriptions riches, ni celle des événements sources.
Un accord riche conserve toutes ces observations. Les records différents
restent révélables par les inspections du contrat récurrent complet.

`attached_agreement_all_futures` conserve toutes les listes finies de demandes,
y compris les refus, par le runner partagé existant. Les demandes suivent
le raccord qui évolue après chaque production : ce n'est pas une comparaison
des mêmes codes d'adresse dans deux présentations différentes. Cette loi
consomme le raccord de l'accord ; les contraintes supplémentaires sur l'ancrage
et les références participantes servent aux lois des descriptions, pas à
une nouvelle preuve de l'exactitude du runner. `outcome` reste la spécification
de référence, sans revendication d'une exécution unique de son évaluateur.

### 32.4. Client fermé : échange trouvé et lectures insuffisantes pour identifier

Le client [InteractionDescriptionAgreementChecks](../../Tests/Relativity/InteractionDescriptionAgreementChecks.lean)
importe uniquement `RelationalPerimeter`. Dans une histoire produite, il
reçoit deux signaux indépendants, exécute le chercheur d'échange, puis transporte
une tête de comparaison déjà stockée. Sa sortie est partagée ; la référence
de la première réception change effectivement de position, de 2 à 1.
Les témoins d'arrivée et d'utilisation restent disponibles après ce transport.
L'égalité avec une exécution de référence est une loi de correction ; elle
n'est pas utilisée comme preuve suffisante de l'absence de réexécution.

Les participants partagent l'ancrage de la comparaison mais leurs records
portent `[one, one]` et `[]`. Les lecteurs de payload et de lecture finale
s'accordent ; les lecteurs complets les distinguent. Un accord riche entre
ces participants est impossible. Deux inspections permises dans le même
curseur révèlent la différence ; ce séparateur ne compare pas deux états
arbitraires au sens de l'équivalence future.

Un second cas exécute deux réceptions distinctes du même signal. Tous les
lecteurs de record s'accordent et les références de réception restent
distinctes. Un accord riche utilisant le raccord identité est alors impossible.
Ce résultat n'interdit pas un autre transport exact, non identitaire, entre
les occurrences : il interdit de transformer leur égalité de lectures en
une identité des sources.

Le client ferme aussi le retour des références, leur composition, le
raffinement commun, l'exactitude des futurs traduits et la persistance des
effets sur tout suffixe fini depuis le successeur de la tête transportée.

### 32.5. Vérifications, fichiers préservés et frontière restante

`lake build +RelationalPerimeter` réussit avec 241 jobs. Les gates complètes
`bash scripts/verify.sh` et `pwsh -NoProfile -File scripts/verify.ps1`
réussissent, la seconde sous Windows natif. Le build complet compte 300 jobs
sans avertissement Lean ; les deux scripts vérifient 298 fichiers Lean et
les 23 fixtures existantes, rejetées pour leurs erreurs et sites attendus.
Les 240 modules de production sont accessibles et strictement stratifiés.
Le nouveau module est H13 et la façade H14 ; les deux contrôleurs imposent
toujours des dépendances descendantes.

L'audit exhaustif porte sur 25 225 constantes de 297 modules, avec 364
exceptions générées par le compilateur et aucune déclaration écrite à la
main dépendante d'un axiome. Les deux fichiers ajoutés ont chacun leur unique
bloc d'audit final ; leurs constructions dans `Type` sont compilées.

Le contrôle local du C généré réemploie les parseurs de corps et de fermetures
statiques de `check-unified-codegen.py`. Sur les 52 racines du nouveau module
et leurs 110 fonctions accessibles, aucun appel au chercheur d'échange,
aux producteurs récurrents, aux runners de demandes ou au calcul de différence
n'est trouvé. Les constructeurs consomment les raccords reçus et les lectures
consomment les records attachés. Les corps de composition transportent les
références et les témoins à travers les deux raccords. Cette inspection locale
complète la vérification du partage existante ; elle ne borne ni les callbacks
arbitraires d'un raccord reçu, ni le coût total, ni la mémoire physique.

Le lot ajoute deux fichiers, en modifie six et n'en supprime aucun. Les
empreintes des 386 autres fichiers du départ local sont identiques, y compris
les deux sources du lot 31, les fondations, le maître, la machine, les contrats,
les cibles canoniques et le registre scientifique. La cible finale de la
section 1 reste inchangée.

Ce lot ferme les accords exacts de descriptions attachées dans le candidat
instrumental existant. Le raffinement des lecteurs n'est ni une précision
numérique ni une nouvelle mesure physique. Aucun oubli runtime n'est autorisé.
L'admission physique de rencontre, `LocationAgreement`, le contrat physique
complet et la reconstruction du domaine relativiste restent à construire.
Il serait faux de déclarer R3.2 physique, le continuum, la métrique ou la
dynamique fermés par ces accords. Aucun commit, push, changement de branche
ou audit extérieur n'est effectué.

## 33. Persistance des accords dans la continuation partagée

### 33.1. Obligation fixée avant l'implémentation

Le départ est `34901a824d9f77d802f41a49a9c527b1953cc07a`, sur `relativite`,
avec un arbre propre. Ce lot poursuit les lois de R3.3 dans le candidat
instrumental existant, sans déclarer fermé leur volet physique.
Les accords du lot 32 doivent maintenant être transportés au long des deux
histoires réellement produites par une continuation partagée.

Prouver le carré des références : prolonger dans la première présentation
puis changer de présentation doit retrouver la référence obtenue en changeant
d'abord de présentation puis en suivant la seconde histoire. Le construire
pour une production, une demande admise ou refusée, puis toute liste finie.
Le raccord final doit être celui de cette même exécution, pas un raccord
reconstruit depuis les valeurs observées.

Le constructeur exécutable doit lier le runner partagé une fois. Les
attachements, leurs accords et les descriptions observées consommeront ses
histoires stockées. Les reprises doivent partir des curseurs qu'il produit ;
la composition des historiques utilisera leurs suffixes stockés. Distinguer
le nombre de productions de la sélection des lecteurs. Prouver l'accord des
restrictions et du raffinement commun après continuation, sans nouvelle
production et sans autoriser un oubli mémoire.

Le client fermé doit partir de l'échange effectivement trouvé du lot 32,
traiter comparaisons, inspections, émission, réception et refus, puis reprendre
depuis le résultat. Les anciennes réceptions et leurs effets révélables
doivent rester distincts. Contrôler les constructions compilées et exécuter
les deux gates. Préserver fondations, maître, machine, anciens contrats et
cible finale. Aucun commit, push, changement de branche ou audit extérieur
n'est autorisé pour ce lot.

### 33.2. Carré des transports sur les productions et les demandes

Le module [ContinuedInteractionDescriptions](../../RelationalPerimeter/Relativity/Production/ContinuedInteractionDescriptions.lean)
prouve `recurring_production_reference_square` à partir des deux productions
et de leurs transports réels. Le cas admis conserve cette loi ; une inspection
ou un refus ne produit aucune occurrence. L'induction de
`shared_run_reference_square` compose les historiques des têtes et suffixes.
Pour chaque référence ancienne, transport dans la première histoire puis
changement de présentation rejoint changement initial puis seconde histoire.
La preuve n'utilise pas l'égalité des valeurs comme substitut à cette référence.

`SharedDescriptionExtension` contient une continuation stockée et ce carré.
Son interface générique admet les exécutions dont ce carré est prouvé ; elle
ne prétend pas rendre canonique toute histoire reçue. `runDescriptionExtension`
ferme l'interface en liant une fois `runSharedRecurring`. Les producteurs,
admissions, refus et traductions restent ceux du contrat récurrent existant.
`description_extension_is_shared_run` fixe cette construction canonique.

Les attachements `first` et `second` suivent les historiques stockés.
Les constructeurs `site` et `rich` consomment le carré et les accords initiaux
pour retrouver l'ancrage, la réception et le signal dans les présentations
finales. Leur raccord est exactement celui de la continuation, non un raccord
calculé après coup depuis les records. Les témoins positifs d'arrivée et de
port utilisés restent transportables sur les mêmes chemins.

### 33.3. Reprise, composition et sélection des lecteurs

`resume` transmet les deux curseurs finaux et leur raccord à une nouvelle
continuation partagée. `append` consomme les deux exécutions stockées : il
compose leurs historiques, leurs rapports et leurs demandes traduites, sans
rejouer les producteurs. Les types exigent le curseur intermédiaire produit.
`appended_description_reference` retrouve chaque référence par les deux voies.

`appendRecurringReport` conserve tous les événements et bits d'admission.
La lecture terminale intermédiaire est `Unit` dans ce contrat ; sa disparition
à la jonction ne supprime aucune lecture informative. Les théorèmes
`appended_description_source_report_exact` et
`appended_description_target_report_exact` raccordent le rapport composé au
contrat sur la liste entière, dans chacune des présentations. Les demandes
de la seconde présentation suivent les traductions successives réelles.

`continued_production_counts` compte seulement les occurrences produites par
les histoires ; ce n'est pas un coût d'évaluation ni un temps physique.
`continued_observation_square` et `continued_refinement_square` conservent les
observations et leurs restrictions après prolongement. Le raffinement commun
du lot 32 demeure disponible pour les attachements prolongés. Choisir ces
lecteurs n'ajoute aucun événement et ne donne aucune autorisation d'effacement.
Des effets différents réfutent encore un accord riche après continuation,
même quand l'accord de leur interaction est conservé.

### 33.4. Client fermé et contrôle du partage compilé

Le client [ContinuedDescriptionChecks](../../Tests/Relativity/ContinuedDescriptionChecks.lean)
importe uniquement `RelationalPerimeter`. Il construit des réceptions réelles,
trouve un échange, transporte une tête stockée et exécute huit demandes :
comparaison, inspection de signal, comparaison refusée, émission, réception,
inspection de lecture, comparaison refusée et comparaison des arrivées
anciennes. Les admissions sont `[true, true, false, true, true, true, false,
true]` ; quatre productions sont constituées dans chaque présentation.

Une reprise inspecte ensuite le signal ancien et compare les deux anciennes
réceptions. Elle est admise par leurs références, leurs témoins d'arrivée
et leur distinction conservée, pas par une valeur d'adresse supposée valide.
Les rapports composés correspondent au contrat entier, les références se
composent et les effets restent observables pour toute liste finie ultérieure.
Un accord d'interaction ne devient toujours pas un accord riche entre les
participants aux records `[one, one]` et `[]`.

Pour éviter une réduction répétée de tout l'objet dépendant pendant
l'élaboration, la définition de test `extension` est marquée `irreducible`.
Son corps reste exécutable ; `extension_is_the_executed_run` prouve son égalité
exacte au constructeur public. Les permissions concrètes sont vérifiées via
l'égalité prouvée avec le runner source de référence. Aucun budget de preuve
n'est relevé et aucune nouvelle hypothèse n'est introduite.

L'inspection locale du C généré, avec les parseurs de corps et de fermetures
statiques existants, confirme un appel du runner partagé dans le constructeur
et un dans la reprise. Les corps transmettent le raccord reçu ou les curseurs
et le raccord réellement produits. Les 19 racines descriptives et leurs 22
fonctions accessibles n'appellent aucun chercheur, producteur ou runner de
demandes. La composition manipule uniquement les historiques, rapports et
demandes stockés. Ce contrôle complémentaire ne certifie ni les callbacks
arbitraires d'un raccord fourni, ni le coût total, ni une réduction mémoire.

### 33.5. Portée et obligations physiques maintenues

Ce lot ferme la persistance des accords dans la continuation partagée et
le raccord des prolongements avec les lecteurs du candidat instrumental.
Il ne donne pas une précision numérique aux lecteurs booléens, ne constitue
pas une rencontre physique et ne produit pas une localisation à partir de
la seule interaction. Il ne ferme pas R3.3 physique, le contrat A4, le continuum,
la métrique ou la dynamique. La cible finale de la section 1 reste inchangée.

### 33.6. Vérifications et périmètre final du lot

Sur l'arbre de travail de `relativite`, issu de
`34901a824d9f77d802f41a49a9c527b1953cc07a` :

- `lake build +RelationalPerimeter` réussit : 242 jobs.
- `scripts/verify.sh` sous Git Bash et `scripts/verify.ps1` sous PowerShell
  natif Windows réussissent : 300 fichiers Lean, build complet de 302 jobs,
  23 fixtures rejetées pour les diagnostics et sites attendus.
- Le balayage couvre 25 343 constantes dans 299 modules ; aucune déclaration
  écrite ne dépend d'un axiome. Les 364 exceptions sont générées par Lean.
- L'inventaire impose les strates de 241 modules de production, tous
  accessibles depuis l'API publique, sans module orphelin. Ce module occupe
  H14 ; la façade passe à H15 sans relâcher les dépendances descendantes.
- Les contrôles documentaires statiques passent. Les 67 liens locaux du plan
  résolvent et la section 1 est identique à celle du commit de départ.
- La comparaison SHA-256 de tous les fichiers hors caches trouve deux ajouts,
  six modifications, 388 fichiers inchangés et aucune suppression. Les quatre
  fondations, le maître, la machine, leurs contrats et le registre scientifique
  sont inchangés. `git diff --check` est propre.

Les deux ajouts sont le module de persistance des accords et son client fermé.
Les six modifications sont la façade, l'import du balayage des constantes,
l'inventaire des strates, ses deux contrôleurs et ce plan. Aucun commit, push,
changement de branche ou audit extérieur n'est effectué dans ce lot.

## 34. Fenêtres numériques sur les lectures constituées

### 34.1. Obligation fixée avant l'implémentation

Sur `relativite`, à partir de `34901a8` et du lot 33 vérifié mais non commité,
traiter le manque numérique de R3.3 : distinguer la sélection de champs des
garanties d'enclosure d'une lecture. La cible de la section 1 ne change pas.
Conserver intégralement le lot 33 et les autres fichiers existants.

Un port numérique choisit soit la réception du participant, soit l'ancrage de
la comparaison effectivement produite. Ses références viennent de l'attachement
constitué ; le lecteur ne reçoit pas une valeur libre à laquelle ajouter une
provenance. Une fenêtre ouverte à bords rationnels donne une demande de
description, non une position géométrique. Le contrôle exécutable doit construire
un certificat sur la valeur réellement lue ou son refus exact, bords exclus.

Prouver les bornes d'erreur depuis la fenêtre, les restrictions par inclusion,
leur identité et composition, et un raffinement commun par intersection lorsque
les deux descriptions sont certifiées sur ce même port. Ne pas postuler la
compatibilité de mesures différentes. Le raffinement ne produit aucune action
et ne modifie ni l'histoire, ni le contrat, ni les effets attachés.

Transporter les certificats par les accords exacts et les historiques stockés
du lot 33. Prouver le carré extension/restriction et la conservation des
valeurs et garanties sans refaire une réception ou une comparaison. Le client
fermé doit varier fenêtres et lectures, rejeter une borne et une fenêtre
inversée, puis poursuivre la même production partagée.

Vérifier l'exécutabilité et l'absence de producteurs dans les chemins numériques
compilés ; exécuter les deux gates. Ne prétendre fermer ni un contrat physique
complet, ni les recouvrements physiques de R4, ni le continuum ou la localisation.
Aucun commit, push, changement de branche ou audit extérieur pour ce lot.

### 34.2. Ports constitués, décision et garanties numériques

[NumericDescriptionWindows](../../RelationalPerimeter/Relativity/Production/NumericDescriptionWindows.lean)
consomme les attachements du lot 33. `AttachedNumericPort` distingue la
réception du participant de l'ancrage de la comparaison. La référence choisie
et sa lecture viennent du même support constitué ; leurs valeurs peuvent
différer, même dans une seule interaction.

`CertifiedNumericReading` porte une valeur fixée par une égalité à la lecture
de ce port exact, ainsi que son appartenance stricte à la fenêtre demandée.
`certifyNumericReading` lit ce port et décide les comparaisons rationnelles :
il retourne ce certificat ou la réfutation de l'enclosure. La demande peut
être inversée ou manquer sa lecture ; elle n'est pas rendue admissible par
un résultat prescrit. `certifiedNumericReadingOfAdmitted` retourne le certificat
de cette même décision exécutée, plutôt que de reconstruire son résultat
depuis une preuve d'admission ; cette égalité est prouvée en production et
dans le client fermé. Les deux bornes sont exclues, et une fenêtre certifiée
a une amplitude positive. Les garanties portent sur les données rationnelles
exactes du candidat, non sur une erreur physique d'instrument non modélisée.

`certified_numeric_error_bounds` borne les deux écarts entre la lecture et
les bords par l'amplitude de la fenêtre. Les bords ne sont ni des distances
primitives ni des coordonnées ; ils décrivent une lecture instrumentale.

### 34.3. Restrictions et intersections compatibles

`WindowRefinement` exprime l'inclusion des bornes, avec identité et composition.
Sa restriction élargit la fenêtre sans changer la lecture constituée.
L'amplitude fine est au plus celle de la fenêtre grossière. Ce n'est ni une
nouvelle mesure, ni un changement de valeur, ni un transport inversible de
toute information.

L'intersection prend le maximum des bornes inférieures et le minimum des
bornes supérieures, par comparaisons exécutables. `CertifiedNumericReading.common`
construit le certificat commun seulement à partir de deux certificats sur
le même attachement et le même port. Leurs deux restrictions retrouvent les
certificats initiaux. L'interface ne promet pas la compatibilité de deux
instruments ou mesures quelconques ; une intersection vide ne reçoit aucun
certificat libre.

### 34.4. Continuation, transport et client fermé

Les prolongements consomment les historiques stockés. Le changement de
présentation consomme l'accord riche exact, pas une égalité numérique seule.
Les valeurs et enclosures sont conservées. Les carrés de prolongement avec
restriction, de transport avec restriction et de continuation partagée
avec changement de présentation sont prouvés. Admission et refus restent
les mêmes sous ces transports ; le contrat récurrent complet est inchangé.

[NumericWindowChecks](../../Tests/Relativity/NumericWindowChecks.lean) importe
uniquement l'API publique. Les lectures initiales un et deux sont des données
reçues explicitement ; deux réceptions réelles suivent chaque émission. Le
lecteur ne produit pas ces données. Sur la lecture un, les fenêtres ouvertes
`(-1, 3)` et `(0, 3)` sont compatibles avec `(-1, 2)` ; leur intersection
est `(0, 2)`. Son amplitude deux est strictement inférieure à l'amplitude
quatre de la fenêtre grossière. La même fenêtre `(0, 2)` refuse la lecture
deux et exclut ses bornes ; une fenêtre inversée est aussi refusée.

La réception lit un tandis que la comparaison produite lit zéro. Les deux
participants peuvent partager une valeur numérique tout en restant des
occurrences distinctes. Une valeur prescrite différente ne peut fournir le
certificat de ce port. Une continuation mêle inspection, comparaison admise
et refus : une seule nouvelle production est constituée. Les garanties
numériques utilisent cet historique stocké ; les reprises sont quantifiées
sur toute liste finie de demandes.

### 34.5. Frontière inchangée

Ce lot construit des descriptions numériques finies et leurs garanties de
restriction dans le candidat instrumental. Il ne prouve ni la fidélité d'un
instrument physique, ni un accord de localisation, ni les règles physiques
de recouvrement de R4. Les garanties d'enclosure ne sont pas une autorisation
d'oubli des effets attachés ou du runtime. Aucun point, continuum, atlas,
métrique ou dynamique relativiste n'est fourni. La cible finale de la
section 1 et les résultats acquis restent inchangés.

### 34.6. Vérifications et périmètre final du lot

Sur les sources finales du lot, avec Lean 4.33.1 :

- `lake build +RelationalPerimeter` réussit : 243 jobs.
- `scripts/verify.sh` sous Git Bash et `scripts/verify.ps1` sous PowerShell
  natif Windows réussissent : 302 fichiers Lean et 304 jobs pour le build
  complet. Les 23 fixtures échouent pour leurs diagnostics et sites attendus.
- Le balayage couvre 25 506 constantes dans 301 modules ; aucune déclaration
  écrite ne dépend d'un axiome. Les 364 exceptions sont générées par Lean.
- Les 242 modules de production sont tous accessibles et stratifiés, sans
  orphelin. Le module numérique est H15, la façade H16 ; les imports locaux
  restent strictement descendants, les strates antérieures inchangées.
- L'inspection complémentaire du C généré couvre 29 racines numériques et
  72 fonctions accessibles, fermetures statiques comprises. Aucun producteur
  local, runner ou chercheur d'échange n'est appelé. Le constructeur admis
  appelle le certifieur une fois et retourne le champ de ce même résultat.
  La normalisation rationnelle reste autorisée et n'est pas déclarée gratuite.
  Ce contrôle ne borne ni les callbacks arbitraires ni le coût total.
- Les contrôles documentaires statiques passent ; les 69 liens locaux du
  plan résolvent et la section 1 est identique au commit de départ.
- Par rapport à l'arbre de début du lot 34, les empreintes SHA-256 trouvent
  deux ajouts, six modifications, 390 fichiers inchangés et aucune suppression.
  Le module et le client du lot 33 sont inchangés, comme les quatre fondations,
  le maître, la machine, les contrats et le registre. Le diff est propre.

Les modifications sont limitées à la façade, l'import de l'audit des constantes,
l'inventaire et ses deux contrôleurs, ainsi qu'à ce plan. Les ajouts sont le
module numérique et son client. Aucun commit, push, changement de branche ni
audit extérieur n'est effectué dans ce lot.

## 35. Contraintes conjointes et premier recouvrement de lectures

### 35.1. Obligation fixée avant l'implémentation

Le départ est `3d8495b849a71bf2243e923cfc3cf9a98c80458d`, sur `relativite`,
avec un arbre propre. Poursuivre R4.1 depuis les attachements et fenêtres des
lots 31-34, sans recevoir de points, de topologie ou de géométrie.

Construire une liste finie de contraintes sur les ports du même attachement
constitué. Sa réalisation positive doit certifier toutes les lectures sur
ce même support ; des compatibilités deux à deux ne la remplacent pas.
Le décideur consomme les résultats du certifieur existant, avec refus exact.
Les restrictions, transports et prolongements réutilisent leurs certificats,
sans réexécuter une production. Le contrat récurrent reste inchangé.

Construire ensuite une première règle de recouvrement instrumental : deux
fenêtres ouvertes strictement plus fines et positivement chevauchantes
couvrent une fenêtre. Le choix d'une branche lit la valeur certifiée et doit
produire son certificat, pas recevoir une branche ou une lecture prescrites.
Composer cette règle dans une grammaire finie et conserver le chemin positif
jusqu'à la fenêtre choisie. La restriction doit retrouver la lecture d'origine.
Le changement exact de description et la continuation stockée doivent
conserver ces choix et ces garanties.

Le client fermé doit réaliser plusieurs ports conjointement, refuser des
contraintes incompatibles sur le même port, choisir effectivement les deux
branches en faisant varier les lectures, traiter le chevauchement et ses
bords, et poursuivre depuis une production partagée. Les différences de
sources et de parcours ne deviennent pas des égalités de valeurs.

Ce recouvrement de lectures ne sera pas nommé `PhysicalCover` : les lois
instrumentales actuelles ne donnent pas encore les localisations physiques
ni leur couverture. Ce lot ne ferme pas la continuité, R4 physique, la
métrique ou la reconstruction relativiste. La cible de la section 1 reste
inchangée. Préserver les fondations, le maître, la machine, les contrats,
les figures et le registre. Vérifier le client public, le code compilé et
les deux gates. Aucun commit, push, changement de branche ou audit extérieur.

### 35.2. Réalisation conjointe sur le même attachement

[ConstitutedReadingConstraints](../../RelationalPerimeter/Relativity/Production/ConstitutedReadingConstraints.lean)
définit des contraintes sur les ports de l'attachement constitué. Le support
n'est pas remplacé par une liste de valeurs libres. `CertifiedReadingConstraints`
est une construction positive dans `Type` : chaque tête porte le certificat
du port exact, et chaque suffixe reste certifié sur le même attachement.

`certifyReadingConstraints` visite structurellement la liste demandée. Chaque
clause visitée appelle une fois le certifieur numérique existant ; le premier
refus termine la décision et réfute la conjonction. En cas d'admission, les
certificats effectivement retournés sont assemblés. L'équivalence
`reading_constraints_admission_exact` relie cette décision à toutes les
contraintes, et `admitted_constraints_are_the_decision_output` fixe le
constructeur admis au résultat de cette même décision.

`ReadingConstraintRefinement` porte positivement les raffinements successifs
des mêmes ports. Identité, composition et restriction sont exécutables ; les
valeurs restent exactement celles des lectures constituées. Deux fenêtres
disjointes sur un même port ne peuvent fournir de réalisation conjointe,
quelle que soit la valeur reçue. Cela ne décide pas l'existence d'un autre
support physique satisfaisant des contraintes libres.

### 35.3. Recouvrement fini et sélection effective

[InstrumentalReadingCovers](../../RelationalPerimeter/Relativity/Production/InstrumentalReadingCovers.lean)
part d'une fenêtre et de deux coupures rationnelles données avec trois
comparaisons strictes : borne inférieure, première coupure, seconde coupure,
borne supérieure. Ces données descriptives justifient le chevauchement et
la réduction stricte des deux amplitudes ; elles ne sont pas une loi physique
de localisation découverte.

`split_cover_exact` prouve que l'appartenance à la fenêtre initiale équivaut
à l'appartenance à au moins une des deux fenêtres fines. `choose` compare
la lecture certifiée à la seconde coupure et construit le certificat de la
branche effectivement retenue. Le chevauchement donne priorité à gauche ;
sa borne supérieure exclue conduit à droite, sans perdre cette lecture.

`InstrumentalReadingCover` compose cette règle dans une grammaire finie.
`Leaf` conserve une dérivation positive du chemin choisi, indexée par ce
recouvrement exact. `select` appelle le choix une fois par noeud visité puis
descend seulement dans la branche choisie. La restriction de sa sortie
retrouve exactement le certificat initial. Le chemin n'identifie ni les
occurrences sources ni leurs parcours.

Le greffage `refine` remplace les feuilles par des recouvrements reçus ;
l'identité et l'associativité sont prouvées. La famille de greffages est un
paramètre descriptif fourni, non un résultat de recherche ou un futur lu
par le producteur. Aucun coût général n'est promis pour ce paramètre.

### 35.4. Raccord conjoint, intersections et continuation

`coverConstraintHead` affine la première contrainte tout en conservant son
suffixe certifié. Sa restriction retrouve la conjonction initiale entière ;
toutes ses valeurs sont conservées. Le recouvrement n'autorise donc ni
l'effacement des autres contraintes ni une réduction de mémoire.

`coveredWindowIntersection` part d'une lecture fine déjà certifiée, la
restreint à la fenêtre du recouvrement, exécute le choix puis construit
l'intersection avec la fenêtre fine. Les deux retours sont exacts. C'est
une intersection localement réalisée sur un même port, pas une preuve de
compatibilité de fenêtres ou d'instruments arbitraires.

Les contraintes et les feuilles choisies se prolongent par les historiques
stockés et se transportent par l'accord riche exact de description. Les
carrés sélection/prolongement, sélection/transport et continuation partagée
sont prouvés, ainsi que les carrés avec restriction. Les valeurs et la
satisfaction conjointe sont conservées sans nouvelle réception, comparaison
ou recherche. Le contrat récurrent complet reste inchangé.

[ReadingCoverChecks](../../Tests/Relativity/ReadingCoverChecks.lean) importe
seulement l'API publique. Une émission, deux réceptions et leur comparaison
produisent réellement son attachement. La réception lit un, la comparaison
zéro ; leur conjonction est certifiée sur ce même attachement. Le client
refuse les contraintes disjointes et une borne externe. Les lectures zéro,
un, deux, trois et trois demis exercent les deux branches, le chevauchement
et ses bords. Le recouvrement composé choisit des chemins différents.
Une continuation mêlant inspection, comparaison admise et refus ne produit
qu'une nouvelle détermination partagée ; ses reprises restent quantifiées
sur toute liste finie de demandes. Les participants restent distincts.

### 35.5. Frontière et prochaine obligation

Ce lot ferme la réalisation de contraintes conjointes sur un attachement
déjà constitué et une première règle finie de recouvrement de ses lectures
instrumentales. Il n'a pas construit un recouvrement de lieux physiques,
une présentation continue complète, une métrique ou la relativité. La
cible de la section 1 reste inchangée.

La suite doit raccorder ces règles finies aux descriptions conjointes et
aux lois admissibles du domaine, en établissant ce que leurs restrictions
et raffinements déterminent effectivement. Elle ne pourra pas substituer
une couverture de valeurs rationnelles à une localisation physique, ni
poser d'avance les points ou la géométrie qu'elle doit reconstruire. R3
physique, R4 physique et les obligations ultérieures restent ouverts.

### 35.6. Vérifications et périmètre final du lot

Sur les sources finales du lot, avec Lean 4.33.1 :

- `lake build +RelationalPerimeter` réussit : 245 jobs.
- `scripts/verify.sh` sous Git Bash et `scripts/verify.ps1` sous PowerShell
  natif Windows réussissent : 305 fichiers Lean, 307 jobs pour le build
  complet et 23 fixtures rejetées pour les diagnostics et sites attendus.
  Aucune erreur ni aucun avertissement Lean ne subsiste.
- Le balayage couvre 25 872 constantes dans 304 modules ; aucune déclaration
  écrite ne dépend d'un axiome. Les 364 exceptions sont générées par Lean.
  Les 41 entrées de l'audit du nouveau client ne dépendent d'aucun axiome.
- Les 244 modules de production sont tous accessibles et stratifiés, sans
  orphelin. Les contraintes sont H16, les recouvrements H17 et la façade H18.
  Les contrôleurs étendent leurs rangs sans assouplir la descente stricte des
  imports. Les strates antérieures restent inchangées.
- L'inspection locale complémentaire du C généré, avec les analyseurs de
  corps et d'accessibilité de `scripts/check-unified-codegen.py`, couvre
  128 racines des deux nouveaux modules et 159 fonctions accessibles,
  fermetures statiques comprises. Aucun producteur, runner récurrent,
  chercheur d'échange ou exécuteur d'extension de description n'y est appelé.
  Le constructeur admis appelle le certifieur une fois ; le sélecteur appelle
  le choix une fois par noeud visité puis seulement la branche choisie.
  Le greffage à callback `refine` est exclu de cette inspection. Celle-ci
  n'est pas une nouvelle gate permanente ni une borne de coût total. Le
  chemin positif compilé conserve aussi des données de l'arbre ; aucune
  minimalité de mémoire n'est revendiquée.
- Les contrôles documentaires statiques passent ; les 72 liens locaux du
  plan résolvent et la section 1 est identique au commit de départ.
- Les empreintes SHA-256 comparées à l'arbre de début du lot trouvent trois
  ajouts, six modifications, 392 fichiers inchangés et aucune suppression.
  Tous les modules antérieurs, les quatre fondations, le maître, la machine,
  les contrats, les figures et le registre sont inchangés. Le diff est propre.

Les modifications sont limitées à la façade, l'import de l'audit des
constantes, l'inventaire et ses deux contrôleurs, ainsi qu'à ce plan. Les
ajouts sont les deux modules de production et leur client public. Aucun
commit, push, changement de branche ou audit extérieur n'est effectué.

## 36. Recouvrements conjoints et intersections finies réalisées

### 36.1. Obligation fixée avant l'implémentation

Poursuivre sur `relativite` depuis le lot 35 vérifié, encore non commité.
Conserver ses neuf fichiers de travail. La cible de la section 1, les
fondations, les productions, le maître et les contrats restent inchangés.

Étendre le choix de fenêtre à toute liste finie de contraintes, sur le même
attachement constitué. Construire positivement les feuilles choisies et
leurs certificats conjoints ; restreindre la sortie doit retrouver toute
l'entrée, pas seulement une égalité de valeurs. Le décideur consomme une
seule décision conjointe et n'impose pas de feuille avant cette décision.

Construire identité et concaténation des recouvrements sans énumérer le
produit de leurs branches. Former l'intersection de deux listes alignées
sur les mêmes ports : son certificat doit consommer leurs deux réalisations
conjointes, avec deux restrictions exactes. Un alignement de ports ou un
recoupement de fenêtres ne fournit pas, à lui seul, cette réalisation.
Raccorder le choix à une réalisation plus fine par une intersection
effectivement certifiée, sans reconstruire une lecture prescrite.

Prouver que ces choix et intersections suivent les accords riches et les
historiques stockés, avec les carrés de restriction et de continuation.
Le client public doit exercer plusieurs ports, deux branches réellement
choisies, une intersection réalisée et une intersection refusée, puis
reprendre le même contrat depuis une production partagée. Contrôler les
chemins compilés et exécuter les deux gates complètes.

Ce sont des recouvrements instrumentaux conjoints, pas `PhysicalCover` ni
un domaine relativiste. Ils ne ferment pas la localisation, les lois de
propagation, les présentations idéales ou le continuum. Aucun changement
de branche, commit, push ou audit extérieur n'est autorisé par ce lot.

### 36.2. Choix conjoints positifs et couverture exacte

[ConjunctiveReadingCovers](../../RelationalPerimeter/Relativity/Production/ConjunctiveReadingCovers.lean)
construit `InstrumentalConstraintCover` sur la liste des contraintes du lot
35. Chaque clause possède son recouvrement de fenêtres justifié ; chaque
sortie `CoveredReadingConstraints` conserve sa feuille locale et son
certificat, puis la sortie de son suffixe sur le même attachement.

La liste fine est calculée depuis ces feuilles, pas reçue comme cible.
`select` consomme les certificats conjoints déjà produits et exécute chaque
choix local une fois. Il ne construit pas la liste de toutes les combinaisons
de feuilles. `decideConjunctiveCover` prend une seule décision conjointe,
puis sélectionne ses certificats retournés ou conserve son refus.

`conjunctive_cover_exact` prouve les deux directions entre satisfaction de
la liste initiale et existence d'une réalisation positive de son recouvrement.
Le témoin exécuté reste disponible dans `Type` ; l'énoncé propositionnel ne
le remplace pas. `selected_joint_cover_restricts` retrouve toute l'entrée.
Les valeurs, tous les ports et leur ordre sont conservés. L'identité garde
la liste et produit des chemins vides ; la concaténation sélectionne les
deux réalisations séparément et assemble exactement leurs sorties.

### 36.3. Intersections effectivement réalisées et retour au grossier

`ReadingConstraintIntersection` construit l'intersection des fenêtres de
deux listes alignées sur les mêmes ports. Cet alignement ne contient ni
valeur ni certificat d'admission. L'intersection peut être vide. Son
équivalence de satisfaction avec la conjonction des deux listes est prouvée.

`certify` consomme deux réalisations entières sur le même attachement pour
former le certificat commun. `realized_intersection_returns` prouve ses
deux restrictions exactes. Ce n'est pas une sélection de mesures seulement
compatibles deux à deux sur des supports indépendants.

`pullbackConjunctiveCover` reçoit une réalisation fine avec son raffinement
de la liste grossière. Il la restreint, exécute le choix conjoint, construit
l'alignement entre la liste sélectionnée et la liste fine, puis certifie
leur intersection depuis ces deux résultats. Les deux retours sont exacts,
ainsi que le retour composé jusqu'à la réalisation grossière d'origine.
La sortie est une paire dépendante positive, non une intersection présumée.
Les lois portent sur ces listes alignées ; elles ne fournissent pas encore
le système général de recouvrements physiques de R4.

### 36.4. Transport, continuation partagée et client public

Les choix conjoints se transportent par l'accord riche et se prolongent par
l'historique stocké. Leur sélection commute avec ces passages ; les chemins
restent identiques. Les restrictions commutent avec transport et prolongement,
et le carré de continuation partagée est prouvé sur toute sortie conjointe.
Les intersections certifiées se transportent et se prolongent de la même
manière. Aucun de ces chemins descriptifs ne produit une nouvelle réception,
comparaison ou recherche.

[ConjunctiveCoverChecks](../../Tests/Relativity/ConjunctiveCoverChecks.lean)
importe seulement l'API publique. Des émissions et réceptions constituent
ses contextes ; la recherche trouve réellement l'échange de deux réceptions
sur anciens ports. La comparaison fournit la tête consommée par son
transport, qui ne la réexécute pas.
Le changement de présentation déplace effectivement la référence de
réception de la position deux à la position un.

La lecture reçue un donne les choix gauche/droite sur les ports réception
et comparaison ; la lecture trois donne droite/droite avec le même
recouvrement. Les sorties contiennent respectivement les valeurs un/zéro
et trois/zéro. Une borne externe est refusée. Une intersection réalisée
rend les deux entrées ; une autre, pourtant alignée, est réfutée pour toute
lecture reçue et refusée par le décideur. Deux ports différents ne peuvent
fournir cet alignement.

La continuation mêle inspection, comparaison et refus, avec une seule
nouvelle production partagée. Les lois suivent l'historique stocké et toutes
les reprises finies du contrat inchangé. Les sources restent distinctes.
Six équations fermées du client demandent une profondeur d'élaboration
locale de 2048 ; elles sont vérifiées par réduction du noyau. Cette limite
de l'élaborateur n'est ni une hypothèse mathématique ni une borne du runtime.

### 36.5. Portée et prochaine obligation

Le raccord des contraintes, de leurs choix conjoints et de leurs
intersections réalisées est désormais exécutable sur les productions
instrumentales existantes. L'ordre constitution, lecture, décision,
sélection et transport reste visible ; il ne devient pas une genèse
géométrique par le seul nom de recouvrement.

Il manque toujours les lois physiques de propagation et de rencontre,
les accords de localisation et les réalisations cohérentes à toute
précision exigées par R4.2. Les recouvrements actuels ne pourront pas être
rebaptisés physiques pour franchir cette frontière. La suite doit établir
leur raccord à ces lois et réalisations, avant de former un domaine de
points, un atlas ou une métrique. La cible de la section 1 est inchangée.

### 36.6. Vérification du lot

Vérification avec Lean 4.33.1, sur l'arbre de travail de `relativite` :

- Le module et le client sont élaborés séparément. Leurs 45 et 41 entrées
  d'audit ne dépendent d'aucun axiome ; aucun avertissement Lean ne subsiste.
- `lake build +RelationalPerimeter` passe avec 246 jobs. Les deux gates
  complètes, Bash et PowerShell natif Windows, passent avec 307 fichiers Lean,
  309 jobs de build et 23 fixtures de rejet vérifiées à leur diagnostic exact.
- Le balayage couvre 26 126 constantes dans 306 modules : aucune déclaration
  écrite ne dépend d'un axiome ; les 364 exceptions sont générées par Lean.
- Les 245 modules de production sont accessibles et stratifiés sans orphelin.
  Le nouveau module est H18 et la façade H19. La descente stricte des imports
  est conservée ; aucune strate antérieure n'est assouplie.
- L'inspection complémentaire du C généré, avec les analyseurs de corps et
  d'accessibilité de `scripts/check-unified-codegen.py`, couvre 99 racines
  du nouveau module et 140 fonctions accessibles. Aucun producteur, runner
  récurrent, chercheur d'échange, exécuteur d'extension de description ou
  énumérateur de produit cartésien n'y est appelé. Le décideur appelle le
  certifieur conjoint une fois ; le sélecteur appelle le sélecteur local une
  fois par clause puis poursuit sur le certificat du suffixe. Le pullback
  réutilise les résultats liés, sans refaire le choix conjoint.
- Cette inspection porte sur les appels statiquement accessibles, pas sur
  des callbacks arbitraires. Ce n'est ni une nouvelle gate permanente ni
  une borne de coût. Les intersections compilées reconstruisent notamment
  les indices de leurs suffixes ; les structures positives conservent aussi
  des données de recouvrement. Aucune optimalité de temps ou de mémoire
  n'est revendiquée par ce lot.
- Les contrôles documentaires statiques passent ; les 74 liens locaux du
  plan résolvent et sa section 1 est identique au commit de départ.
- Les empreintes SHA-256, comparées à l'arbre de début du lot, donnent deux
  ajouts, six modifications, 395 fichiers inchangés et aucune suppression.
  Les modules et le client du lot 35, les quatre fondations, le maître, la
  machine, les contrats, les figures et le registre sont inchangés. Le diff
  est propre.

Les six modifications concernent la façade, l'import de l'audit des
constantes, l'inventaire et ses deux contrôleurs, ainsi que ce plan. Les
deux ajouts sont le module de production et son client public. Aucun commit,
push, changement de branche ou audit extérieur n'est effectué.

## 37. Raffinements réalisés à toute précision demandée

### 37.1. Obligation fixée avant l'implémentation

Poursuivre le premier volet de R4.2 depuis le lot 36 : toute liste de lectures
déjà certifiées doit fournir, pour chaque précision rationnelle positive
demandée, une liste fine réalisée, une restriction exacte et une borne sur
la largeur de chaque fenêtre. Construire les fenêtres depuis ces lectures,
puis leur intersection avec les contraintes antérieures ; ne pas recevoir
une liste fine présumée habitée. La précision reste descriptive, distincte
du nombre de productions physiques et de la longueur des continuations.

Construire les reprises de cette opération pour toute liste finie de
précisions, sans plafond global. Chaque tête lit ses certificats reçus et
sa seule précision ; la queue reprend ses certificats produits. Prouver le
retour composé, la concaténation des reprises et la compatibilité avec les
transports et historiques stockés. Consommer les feuilles du recouvrement
déjà sélectionné, sans relancer sa sélection ni la production instrumentale.

Étendre le client public du lot 36, sans une nouvelle instance de production :
plusieurs ports, plusieurs précisions, continuation partagée, changement
effectif de référence et refus antérieurs conservés. Vérifier l'élaboration,
les audits, le code compilé et les deux gates complètes.

Ce lot ne construit pas le deuxième volet de R4.2 : les localisations qui
ne sont pas déjà les descriptions d'un événement exécuté. Il ne ferme ni
les lois physiques de propagation et de rencontre, ni `PhysicalCover`, ni
le domaine relativiste. La cible reste inchangée. Les onze fichiers de
travail antérieurs sont préservés ; aucun commit, push, changement de branche
ou audit extérieur n'est autorisé.

### 37.2. Précision construite et réalisation de toutes les clauses

[PreciseReadingRefinements](../../RelationalPerimeter/Relativity/Production/PreciseReadingRefinements.lean)
réemploie `Precision` du backend numérique existant. Sa valeur et celle de
sa demi-précision sont strictement positives, avec une preuve fermée. Pour
une lecture certifiée, `ReadingWindow.atPrecision` calcule les bords autour
de sa valeur reçue ; sa largeur est exactement la précision demandée.
`refineReadingPrecision` intersecte cette fenêtre avec la fenêtre antérieure
et construit le certificat commun. Il répète ce passage pour toutes les
clauses, sur le même attachement, avec leurs ports inchangés.

La liste fine est produite depuis les certificats ; elle n'est pas un
paramètre libre. `reading_precision_restricts_exactly` rend toute la liste
reçue et `reading_precision_bounds_every_window` borne chaque fenêtre fine.
Les certificats positifs donnent aussi leur réalisation ; une borne seule
ne fournit pas une lecture admise. `RealizedReadingRefinement` conserve la
liste fine, son raffinement positif et ces certificats. Cette interface
descriptive est distincte d'une autorisation de production physique.

### 37.3. Reprises finies arbitraires et retour composé

`refineReadingPrecisions` récure structurellement sur la liste de précisions.
Sa tête calcule une seule fois le raffinement de la liste reçue ; sa queue
consomme les certificats de ce résultat. Elle ne reçoit ni point extérieur
ni queue de productions physiques. La composition des raffinements construit
le retour jusqu'à la liste initiale. Les lois d'identité et d'associativité
portent sur les témoins positifs de liste, pas seulement leurs valeurs.

`precision_runs_append` identifie exactement une course concaténée à la
reprise de son résultat intermédiaire. `resume` accepte ce résultat déjà
produit : il ne réexécute pas le préfixe. Le retour composé, toutes les
valeurs et tous les ports sont conservés. Chaque précision appartenant à
la liste reste une borne de toutes les fenêtres finales, même après une
demande moins fine. Cette propriété est prouvée pour toute liste finie,
sans horizon maximal ni sélection implicite d'une famille infinie.

Le module transporte ces résultats par les accords riches et les historiques
stockés. La course entière commute avec ces deux passages ; son carré de
continuation utilise la même production partagée. `CoveredReadingConstraints.precise`
consomme les certificats des feuilles déjà sélectionnées, sans appeler de
nouveau le sélecteur de recouvrement. Sa restriction composée retrouve le
certificat grossier de ce choix.

### 37.4. Client existant, distinctions et frontière

Le [client public du lot 36](../../Tests/Relativity/ConjunctiveCoverChecks.lean)
est étendu sans nouvelle entrée maître ni copie du scénario. Il demande les
précisions un puis un demi sur ses réceptions et comparaison réelles.
Les fenêtres changent effectivement, toutes les clauses restent présentes,
les valeurs restent un et zéro, et la restriction rend les certificats
initiaux. La reprise depuis le premier résultat égale la course complète.
Les lois sont aussi exercées sur des listes arbitraires de précisions.

Les lectures reçues un et trois ne peuvent pas donner les mêmes fenêtres
fines : leur écart contredit la largeur certifiée. Une précision non positive
ne peut être construite ; une conjonction antérieure réfutée ne fournit pas
les certificats nécessaires pour commencer ce chemin. Le transport déplace
toujours la référence réelle de réception ; la continuation utilise le même
historique stocké, sans changer le contrat de toutes les reprises finies.
Trois nouvelles preuves du client utilisent la profondeur d'élaboration
locale de 2048 déjà employée pour ses données constituées ; aucune limite
globale du runtime ni hypothèse de preuve n'est ajoutée.

Ce lot ferme les raffinements instrumentaux réalisés à toute précision
rationnelle positive demandée, pas `PhysicalPresentation`. Il traite les
descriptions des déterminations déjà constituées, et non la deuxième
obligation de R4.2. Les lois physiques de propagation, l'admission de rencontre,
les accords de localisation et les réalisations cohérentes non réduites aux
noms d'événements exécutés restent nécessaires avant la reconstruction du
domaine. La cible de la section 1, les fondations, le maître et les contrats
restent inchangés. Aucune borne de coût, minimalité mémoire ou validation
relativiste n'est déduite de ces fenêtres exactes.

### 37.5. Vérifications et périmètre final du lot

Vérification sur `relativite`, avec Lean 4.33.1 inchangé :

- Le nouveau module et le client public étendu s'élaborent séparément.
  Leurs 44 et 63 entrées d'audit n'affichent aucun axiome ni avertissement
  Lean. Les 41 entrées antérieures du client sont conservées.
- `lake build +RelationalPerimeter` passe avec 247 jobs. Bash et PowerShell
  natif Windows vérifient chacun 308 fichiers Lean, un build de 310 jobs et
  les 23 fixtures de rejet avec leurs diagnostics exacts. Les contrôleurs
  du maître, de la machine et des agents passent sans modification.
- Le balayage exhaustif couvre 26 221 constantes dans 307 modules : aucune
  déclaration écrite ne dépend d'un axiome ; les 364 exceptions sont générées
  par Lean. Le scan des sources ne trouve aucun terme interdit.
- Les 246 modules de production sont stratifiés et accessibles, sans
  orphelin. Le nouveau module est H19 et la façade H20 ; le backend numérique
  reste en amont et la descente stricte des imports est conservée.
- L'inspection locale du C généré, avec les analyseurs de
  `scripts/check-unified-codegen.py`, couvre 31 racines du nouveau module
  et 63 fonctions accessibles. Aucun producteur, runner récurrent, chercheur
  d'échange ou sélecteur de recouvrement n'est accessible depuis ces racines.
  Le chemin de clause construit sa fenêtre une fois et recurse une fois
  sur les autres certificats reçus. Le chemin de précisions construit sa
  tête une fois puis passe ses champs `fine` et `readings` au suffixe. Le
  chemin `resume` lit ceux du résultat reçu, sans reprendre son ancien run.
- La demi-précision numérique est partagée entre les deux bords dans le C
  inspecté. Cependant, ce chemin utilise toujours la normalisation rationnelle
  du backend existant, avec sa recherche finie de représentant. Il conserve
  aussi des indices de fenêtres et des témoins de raffinement en `Type`.
  L'inspection n'est pas une borne de coût ou une minimalité mémoire, ni une
  gate permanente supplémentaire pour des callbacks arbitraires.
- Les contrôles documentaires statiques passent, les 76 liens locaux du
  plan résolvent et la cible de la section 1 est inchangée. Le diff est propre.
- Les empreintes SHA-256 comparées au début du lot donnent un ajout, six
  modifications, 397 fichiers inchangés et aucune suppression. Les quatre
  fondations, tous les anciens modules de production, le maître, la machine,
  les contrats, le registre et les figures sont inchangés, hors de la façade
  enrichie par le nouvel import et ses audits.

L'ajout est le module de raffinements. Les modifications sont le client
public étendu, la façade, l'inventaire et ses deux contrôleurs, ainsi que ce
plan. Aucun commit, push, changement de branche ou audit extérieur n'est
effectué. Le lot instrumental est vérifié ; les obligations physiques
énoncées en 37.4 et la cible finale restent ouvertes.

## 38. Compatibilité des descriptions et séparation des lectures

### 38.1. Obligation fixée avant l'implémentation

Poursuivre le premier volet de R4.2, sans le confondre avec son second
volet physique. Deux courses finies de précision issues des mêmes
certificats constitués doivent fournir un raffinement conjoint positif,
avec retour exact aux deux descriptions reçues puis aux certificats
initiaux. La construction consomme les résultats déjà calculés ; elle
ne rejoue ni leurs courses de précision, ni la sélection de recouvrement,
ni une production instrumentale. Le raccord doit suivre les transports
riches et la continuation partagée du même contrat.

Fermer aussi une limite exacte de ces lecteurs : sur les ports constitués,
deux lectures rationnelles différentes doivent fournir effectivement une
fenêtre qui admet la première et refuse la seconde. L'accord de toutes
les admissions par fenêtres doit être équivalent à l'égalité des valeurs
lues, et non à l'égalité des occurrences ou à un accord de localisation.
Le séparateur est une donnée positive calculée depuis les deux lectures
reçues ; aucune existence de fenêtre n'est laissée comme hypothèse.

Le client public existant doit établir les retours pour deux résolutions,
un refus positif entre lectures différentes, et l'accord numérique de
participants dont les occurrences restent distinctes. Il réutilise les
mêmes productions et la même continuation, sans nouvelle instance maître.

Ce lot ne définit pas un domaine de points, une mesure physique, un accord
de localisation ni une loi de propagation. Les familles descriptives
restent attachées à des déterminations déjà produites. Les réalisations
constitutives compatibles qui ne sont pas réduites à ces événements finis,
ainsi que les lois physiques de R3-R7, restent à construire. La cible de
la section 1 et les contrats acquis ne sont pas modifiés.

### 38.2. Raffinement conjoint des résultats reçus

Le module [ReadingCompatibility](../../RelationalPerimeter/Relativity/Production/ReadingCompatibility.lean)
forme `RealizedReadingRefinement.common` depuis deux résultats sur le même
attachement et la même liste initiale de contraintes. Il construit l'alignement
de leurs ports depuis leurs raffinements positifs, puis certifie leurs
intersections avec les deux listes de certificats déjà reçues. Les fenêtres
communes sont calculées, et non prescrites comme résultat du constructeur.

`realized_common_returns` retrouve les deux listes de certificats complètes,
pas seulement leurs valeurs. `realized_common_coarse_returns` compose chacun
de ces retours avec sa restriction initiale. Pour deux courses quelconques
de précisions finies depuis les mêmes certificats,
`precision_courses_common_return` ferme les deux retours à ces certificats.
Les bornes de précision des deux côtés sont conservées dans le raffinement
commun. Les lois de prolongement, de transport riche et le carré de la
continuation partagée portent sur tout le résultat.

`CommonReadingRefinement` est une interface descriptive positive, indexée
par les deux listes de contraintes, et non un certificat de causalité ou de
localisation. Ses retours exacts sont démontrés pour le producteur construit
`common`, pas postulés pour une structure libre. Cette indexation évite de
demander une égalité d'encodage des résultats intermédiaires pour effectuer
le transport des mêmes lectures.

### 38.3. Ce que les lecteurs numériques déterminent exactement

`separateNumericReadings` lit les deux ports constitués reçus. Il décide
l'égalité des valeurs rationnelles. En cas de différence, il compare leur
ordre et construit une fenêtre : le bord excluant est la valeur du second
port ; l'autre bord vient de la fenêtre positive construite autour du
premier. Le résultat positif porte le certificat du premier et le refus
du second par cette même fenêtre. Les deux directions d'ordre sont closes.

`numeric_separator_admissions` relie ces données aux admissions du code,
avec `true` pour le premier port et `false` pour le second.
`numerical_readers_determine_values` prouve les deux sens : l'accord de
toutes les admissions par fenêtres équivaut exactement à l'égalité des
valeurs de ces ports. `joint_numerical_readers_determine_values` étend ce
résultat aux conjonctions finies et aux deux ports numériques. Aucun témoin
de séparation requis n'est laissé dans une existence propositionnelle.

Ces équivalences sont des propriétés de ces lecteurs, pas des accords de
localisation, de provenance, de parcours ou de mémoire complète. Le client
[ConjunctiveCoverChecks](../../Tests/Relativity/ConjunctiveCoverChecks.lean)
réutilise les réceptions et la comparaison existantes. Les valeurs un et
trois produisent deux séparateurs orientés, dont le bord refusé vient bien
de la seconde lecture. La même lecture de comparaison ne détermine pas
l'arrivée. Inversement, deux participants ont toutes leurs admissions
numériques égales tout en conservant des références d'occurrence prouvées
distinctes. Un accord numérique ne peut donc devenir leur identification.

Le séparateur conserve sa fenêtre et ses deux garanties sous les transports
riches et les histoires déjà produites. Le raffinement conjoint suit la même
continuation partagée ; le contrat de toutes les suites finies est inchangé.
Quatre limites de profondeur supplémentaires sont locales aux équations du
client fermé : elles règlent son élaboration, pas la longueur des courses.
Aucune limite de heartbeats n'est augmentée.

### 38.4. Frontière de la cible

Ce lot ferme la compatibilité positive de plusieurs descriptions finies des
mêmes lectures déjà produites et la portée exacte de leurs lecteurs numériques.
Il ne fournit pas les réalisations physiques cohérentes du second volet de
R4.2, ni un domaine de localisations ou sa structure relativiste. L'égalité
numérique établie ne remplace pas les lois de propagation, de rencontre et
de transport physique nécessaires à ces localisations. La cible finale de
la section 1 reste ouverte et inchangée ; aucune conclusion de complexité,
de minimalité mémoire ou de mesure physique n'est ajoutée.

### 38.5. Vérifications et périmètre final du lot

Vérification sur `relativite`, avec Lean 4.33.1 inchangé :

- Le nouveau module s'élabore avec ses 24 entrées d'audit sans axiome.
  Le client étendu s'élabore avec 86 entrées, dont les 63 précédentes
  conservées et 23 nouvelles ; aucune ne dépend d'un axiome.
- `lake build +RelationalPerimeter` passe avec 248 jobs. Les gates Bash
  et PowerShell natif Windows passent toutes deux : 309 fichiers Lean,
  build complet de 311 jobs et 23 fixtures de rejet avec leurs diagnostics
  exacts, sans erreur étrangère. Aucun avertissement Lean n'est émis.
- Le balayage exhaustif couvre 26 316 constantes dans 308 modules :
  aucune déclaration écrite ne dépend d'un axiome. Les 364 exceptions
  proviennent de déclarations générées par Lean. Le scan sensible à la
  casse des sources ne trouve aucun terme interdit.
- Les 247 modules de production sont accessibles et strictement stratifiés,
  sans orphelin. Le module d'accord de lectures est H20, la façade H21 ;
  aucun autre rang ni droit d'import n'est changé.
- L'inspection complémentaire du C utilise les analyseurs existants de
  `scripts/check-unified-codegen.py`. Elle couvre les 36 racines du nouveau
  module et 90 fonctions statiquement accessibles. Aucun appel nommé à un
  producteur, runner récurrent, chercheur d'échange, raffineur de précision
  ou sélecteur de recouvrement n'est accessible. Le constructeur commun
  lit les deux raffinements et certificats reçus, puis appelle une fois
  l'alignement et une fois la certification conjointe.
- Dans le corps C du séparateur, chaque port est lu une fois. La fenêtre
  centrée est construite une fois, uniquement après détection d'une
  différence ; son bord conservé et la seconde valeur forment la fenêtre
  retournée. L'extraction positive depuis une différence prouvée appelle
  le discriminateur une fois et conserve son résultat. Ces constats portent
  sur les appels statiques inspectés. Les 17 sites de callbacks transitifs,
  notamment les lectures du support reçu, ne sont pas une garantie globale
  sur les fonctions d'un client. Le backend de normalisation rationnelle
  existant reste utilisé ; aucune borne de coût n'est déduite.
- Les contrôles documentaires passent, les 78 liens locaux du plan résolvent,
  sa section 1 est strictement inchangée et `git diff --check` est propre.
  Le seul avertissement Git concerne la conversion LF/CRLF de l'inventaire.
- Les empreintes SHA-256 comparées au début de ce lot montrent un ajout,
  six modifications, 398 fichiers inchangés et aucune suppression. Les
  quatre fondations, tous les anciens modules de production hors façade,
  le maître, la machine, les contrats, le manifeste Lean, le registre et
  les figures sont inchangés. Les lots précédents sont préservés.

L'ajout est `ReadingCompatibility.lean`. Les modifications portent sur le
client public existant, la façade, l'inventaire et ses deux contrôleurs,
ainsi que le plan. Aucun commit, push, changement de branche ou audit
extérieur n'est effectué. Ce lot descriptif est vérifié ; la frontière
physique de 38.4 et la cible finale restent ouvertes.

## 39. Composition des recouvrements depuis les choix déjà produits

### 39.1. Obligation fixée avant l'implémentation

La composition descriptive de R4.1 existe pour un remplacement uniforme
des fenêtres, mais son sélecteur n'a pas encore de raccord public avec une
reprise depuis la feuille déjà choisie. Fermer ce passage pour des
remplacements finis distincts à chaque feuille, puis pour toutes les clauses
conjointes. Chaque remplacement sera une donnée positive indexée par
l'arbre reçu, et non un callback pouvant produire une fenêtre arbitraire.

La reprise doit suivre le chemin stocké, sélectionner uniquement dans son
recouvrement suffixe et conserver le préfixe de choix. Prouver son égalité
complète avec la sélection du recouvrement composé, ses retours exacts,
sa composition et les carrés de transport et de continuation. Le suffixe
reçoit les certificats retournés, pas des lectures reconstruites librement.
Le client public existant doit exercer un suffixe qui prend réellement une
nouvelle décision ; une identité seule ne suffit pas à ce contrôle.

Ce lot ferme une loi de consommation des recouvrements instrumentaux.
Il ne constitue pas de nouvelles réalisations physiques et ne ferme pas
le second volet de R4.2. Les primitives actuelles ne deviennent pas des
lois de localisation par composition de fenêtres. La cible de la section 1,
les contrats, les fondations et l'instance maître restent inchangés.
La demande autorise l'implémentation et ses vérifications, sans commit,
push, changement de branche ni audit extérieur.

### 39.2. Construction et portée des égalités

Le module [ContinuedReadingCovers](../../RelationalPerimeter/Relativity/Production/ContinuedReadingCovers.lean)
construit `ReadingCoverSubstitution`, un arbre positif de remplacements
indexé par le recouvrement reçu. `atLeaf` suit la feuille enregistrée et
retrouve son remplacement. `resume` sélectionne dans ce seul suffixe avec
le certificat reçu, puis greffe son chemin au préfixe. Le préfixe n'est pas
resélectionné. `resumed_cover_keeps_the_prefix` démontre exactement cette
concaténation ; le retour retrouve le certificat initial complet.

`composed_cover_selection_is_resumption` porte sur tout le résultat et non
sur sa seule valeur. Son hypothèse précise est que le choix initial vient
du sélecteur du recouvrement initial. Un autre choix positif dans une zone
de chevauchement reste admissible pour `resume`, mais cette égalité avec le
sélecteur canonique n'est pas revendiquée pour lui. Cette distinction est
nécessaire : conserver un choix reçu et choisir à nouveau sont deux actes
différents.

`ConstraintCoverSubstitution` reprend toutes les clauses conjointes. Ses
retours conservent leurs certificats et leurs valeurs. La composition
structurelle des substitutions calcule exactement le recouvrement final.
`ReadingCoverCourse` enchaîne un nombre fini arbitraire de reprises : chaque
suffixe reçoit le choix calculé par la reprise précédente. L'induction
prouve le retour à tous les certificats initiaux et l'égalité complète avec
la sélection finale lorsque le préfixe était canonique. Les carrés de
prolongement, de transport riche et de continuation partagée sont fermés
pour les reprises conjointes et pour toutes ces courses.

Ces arbres sont des instructions descriptives reçues, pas des productions
physiques ni une découverte de lois physiques. La course ne prend pas une
histoire instrumentale achevée pour produire son préfixe. Le transport
utilise la continuation partagée existante, sans nouveau maître ni nouveau
contrat. Aucune égalité de lectures ne devient une identité d'occurrences.

### 39.3. Client concret et distinction contre une resélection

Le client [ConjunctiveCoverChecks](../../Tests/Relativity/ConjunctiveCoverChecks.lean)
reprend les mêmes réceptions, la même comparaison et le même échange de
présentation déjà constitués. Des suffixes non identitaires donnent les
chemins `[[true,true],[false,true]]` pour la lecture un et
`[[false,false],[false,true]]` pour la lecture trois. Les équations sont
vérifiées par le noyau. Le client ferme les retours complets, les ports,
les valeurs et les carrés utilisant l'histoire déjà calculée.

Une lecture un admet aussi un choix positif reçu dans le chevauchement,
avec le chemin `[true,false]`. Sa reprise identitaire conserve ce chemin,
alors que rejouer le sélecteur initial donnerait `[true,true]` : les deux
chemins sont prouvés différents. Ce choix est une entrée descriptive
admissible, et non une seconde exécution maître. Le contrôle distingue
donc effectivement la consommation du choix reçu d'une resélection.

Le raccord aux précisions existantes retrouve les certificats initiaux et
conserve la dernière borne demandée. Des contraintes incompatibles ne
peuvent fournir de choix positif à reprendre. Quatre limites de profondeur
locales règlent uniquement les équations fermées de chemins du client ;
elles ne bornent pas les courses. Aucun heartbeat n'est augmenté.

### 39.4. Inspection complémentaire du code compilé

L'inspection en lecture seule utilise les analyseurs existants de
`scripts/check-unified-codegen.py`. Depuis les 77 racines du nouveau module,
89 fonctions sont statiquement accessibles. Aucun appel nommé à une
production instrumentale, au runner récurrent, au chercheur d'échange ou
au raffineur de précision n'y est accessible. La fermeture de `atLeaf` ne
contient aucun sélecteur : son corps suit seulement le chemin enregistré.

Le corps compilé de la reprise locale appelle une fois `atLeaf`, une fois
le sélecteur sur le remplacement ainsi obtenu, puis greffe une fois le
chemin. Il réemploie la fenêtre et le certificat retournés. La reprise
conjointe consomme chaque clause ; la course appelle cette reprise une
fois avant de continuer avec son résultat.

Le constructeur conjoint matérialise aussi les indices positifs de
recouvrement par `flatten`. Ce travail représentatif est présent : il
n'est ni déclaré gratuit ni confondu avec une nouvelle décision de
sélection. Les cinq sites de callbacks transitifs ne garantissent pas
le comportement de fonctions arbitraires fournies par un client. Cette
inspection ne démontre ni une borne de coût globale, ni une taille mémoire
minimale, ni une incarnation physique ; ce n'est pas un audit indépendant.

### 39.5. Vérifications et frontière restante

Vérification sur `relativite`, avec Lean 4.33.1 inchangé :

- Le nouveau module et ses 38 entrées d'audit s'élaborent sans axiome.
  Le client public s'élabore avec 120 entrées : les 86 précédentes et
  34 nouvelles. Aucun avertissement Lean n'est émis.
- `lake build +RelationalPerimeter` passe avec 249 jobs. Les vérifications
  complètes Bash et PowerShell natif Windows passent toutes deux sur
  310 fichiers Lean ; le build complet compte 312 jobs. Les 23 fixtures
  de rejet échouent aux sites et pour les diagnostics attendus, sans
  erreur étrangère.
- Le balayage exhaustif couvre 26 527 constantes dans 309 modules,
  avec zéro exception écrite et 364 exceptions générées par Lean. Le
  scan des sources exclut tous les termes interdits et chaque fichier
  garde exactement un bloc d'audit final.
- Les 248 modules de production sont accessibles et stratifiés, sans
  orphelin. L'ajout est H21 et la façade passe en H22 ; les rangs et
  les droits d'import des autres couches restent inchangés.
- Les contrôles documentaires et les références Lean passent. La section
  1 du plan reste strictement inchangée. `git diff --check` est propre ;
  le seul avertissement Git concerne la conversion LF/CRLF de l'inventaire.
- La comparaison SHA-256 depuis le début du lot montre un ajout, six
  modifications, 399 fichiers inchangés et aucune suppression. Les quatre
  fondations, tous les anciens modules de production hors façade, le
  maître, la machine, les contrats, le manifeste Lean, le registre et
  les figures restent inchangés.

Les modifications sont limitées au nouveau module, à la façade, au client
public existant, à l'inventaire et à ses deux contrôleurs, ainsi qu'au plan.
Aucun commit, push, changement de branche ou audit extérieur n'est effectué.
Les lecteurs et traductions du registre qui attendaient une revue restent
en attente ; leur statut n'est pas remplacé par celui de ces vérifications.

La loi descriptive de reprise depuis les choix positifs est fermée pour
des courses finies de longueur arbitraire. Les réalisations constitutives
physiques compatibles du second volet de R4.2, puis les lois physiques et
la reconstruction exacte du domaine relativiste, restent ouvertes. Une
composition de fenêtres sur des lectures déjà produites ne les remplace
pas. La cible finale est conservée, mais n'est pas déclarée atteinte.

## 40. Restriction et intersection sans remplacer le choix reçu

### 40.1. Obligation fixée avant l'implémentation

Le pullback existant sélectionne un recouvrement depuis les certificats
restreints. Il convient pour un choix canonique, mais ne préserve pas un
autre choix positif déjà reçu dans un chevauchement. Construire le raccord
complémentaire : consommer ce choix et une réalisation plus fine sur le
même attachement, former leur intersection avec les constructeurs existants,
puis retrouver le choix complet avec ses feuilles enregistrées. Ne pas
rejouer le sélecteur initial pour ce retour.

La reprise et toute course finie de reprises devront pouvoir consommer
ce retour, avec une égalité complète à leur résultat antérieur et les
carrés de transport et de continuation partagée. Exercer un choix reçu
non canonique : son chemin doit rester conservé après l'intersection,
alors qu'une resélection le changerait. Les réalisations incompatibles ne
seront pas admises par un alignement seul.

Ce lot complète la stabilité descriptive de R4.1. Il ne fournit pas de
nouvelles réalisations physiques, ne ferme pas le second volet de R4.2
et ne modifie ni la cible ni les contrats. La demande n'autorise aucun
commit, push, changement de branche ou audit extérieur.

### 40.2. Deux retours différents, avec leurs données propres

Le module [RestrictedReadingCovers](../../RelationalPerimeter/Relativity/Production/RestrictedReadingCovers.lean)
ne remplace pas le pullback existant. Celui-ci calcule un choix depuis des
certificats restreints ; le nouveau passage conserve un choix déjà reçu.
`CoveredReadingConstraints.realized` extrait ses contraintes, son raffinement
positif et ses certificats. `intersect` appelle le producteur commun existant
avec cette réalisation et la réalisation plus fine reçue. Les deux retours
retrouvent exactement leurs certificats, puis leurs sources grossières.

`recoverIntersection` forme cette intersection une fois, puis appelle
`recoverFromIntersection`. Cette seconde entrée consomme une intersection
déjà produite : elle restreint ses certificats du côté du choix initial et
les rattache aux mêmes feuilles par `withReadings`, sans reformer la
réalisation commune. `withReadings` suit structurellement les choix positifs,
sans appeler de sélecteur ni lire de nouveau les instruments. Le résultat est
égal au choix complet reçu, y compris ses chemins, et pas seulement à une
liste de valeurs. Une restriction numérique seule ne permettrait pas de
reconstruire un choix non canonique ; les feuilles reçues restent donc des
données nécessaires à cette opération de retour.

La preuve d'égalité utilise l'exactitude des certificats sur le même
attachement et les mêmes fenêtres. Elle vaut pour tout certificat ainsi
indexé : elle ne prétend pas que l'intersection est logiquement indispensable
pour recopier un choix. La construction exécutée de l'intersection, ses deux
retours et son utilisation par le code sont des obligations distinctes,
vérifiées séparément. Aucun résultat de causalité physique n'en est inféré.

### 40.3. Reprise, continuation et client fermé

`resumeAfterIntersection` forme et utilise le retour, puis appelle
la reprise déjà construite. `runAfterIntersection` raccorde ce même passage
à toute course finie de longueur arbitraire. Lorsqu'une intersection est
déjà disponible, `resumeFromIntersection` et `runFromIntersection` la
consomment directement, sans répéter sa formation. Leurs égalités portent sur
tout le résultat, sans adaptation de carrier. Les retours aux certificats
initiaux et les carrés de prolongement, de transport riche et de continuation
partagée sont prouvés sur les données effectivement reçues.

Le client [ConjunctiveCoverChecks](../../Tests/Relativity/ConjunctiveCoverChecks.lean)
réemploie les mêmes réceptions, la comparaison et la continuation partagée.
Il forme l'intersection avec la précision produite une seule fois et fait
consommer ce résultat enregistré par le retour et les entrées partagées.
Il ferme les deux retours,
la conservation de la source et le passage au suffixe non identitaire du
lot 39. Les lois de course sont exercées pour toute course reçue.

Le choix positif non canonique du chevauchement devient une réalisation
conjointe à un port, puis reçoit une précision calculée. Son intersection
retrouve les deux listes de certificats ; le retour conserve le chemin
`[[true,false]]`, prouvé différent de `[[true,true]]` qu'une resélection
aurait choisi. La borne de la réalisation fine est conservée dans
l'intersection. Une seule limite de profondeur supplémentaire est locale
à cette équation fermée ; aucun heartbeat n'est augmenté. Les refus et les
séparateurs précédents restent conservés dans le même client.

### 40.4. Ce que montre le code compilé

L'inspection complémentaire, en lecture seule, utilise les analyseurs
existants de `scripts/check-unified-codegen.py`. Elle couvre les 30 racines
du nouveau module et 59 fonctions statiquement accessibles. La formation
de l'intersection, les deux entrées de retour et `withReadings` n'atteignent aucun sélecteur
ni chooser. Aucun producteur instrumental, runner récurrent, chercheur
d'échange ou raffineur de précision n'est accessible depuis ces racines.

Le corps compilé d'`intersect` appelle une fois le raffinement commun.
`recoverIntersection` appelle une fois l'intersection, puis une fois le
retour partagé. Celui-ci appelle une fois la restriction et une fois le
rattachement des certificats. `withReadings` reprend les
fenêtres et les feuilles enregistrées, installe les certificats reçus et
continue sur le suffixe correspondant. Les quatre wrappers appellent une
fois leur entrée de retour puis, respectivement, une fois la reprise ou
une fois la course, avec le résultat retourné. Les trois entrées qui
consomment l'intersection enregistrée n'atteignent ni le producteur commun
ni son constructeur d'alignement. Aucun travail ancien n'est rejoué pour
reconstruire le préfixe de décisions.

Les contraintes, raffinements et certificats ont un encodage effectif et
sont parcourus. La construction du raccord gauche recalcule notamment
des intersections de fenêtres ; elle ne reconstitue pas la réalisation
commune ni ses certificats. Ce travail n'est pas déclaré nul. Aucun site de callback
dynamique n'apparaît dans cette fermeture statique ; ce constat ne couvre
pas tous les appels qu'un client pourrait ajouter. Il ne constitue ni une
borne de coût global, ni une preuve de minimalité physique, ni un audit
indépendant. L'accord numérique ne permet aucun oubli de données du contrat.

### 40.5. Vérifications finales et portée du lot

Sur `relativite`, avec Lean 4.33.1 inchangé :

- Les 35 entrées d'audit du nouveau module et les 146 du client public
  s'élaborent sans axiome. Le client conserve toutes les déclarations
  précédentes et ajoute 26 entrées pour ce lot.
- `lake build +RelationalPerimeter` passe avec 250 jobs. Les gates
  complètes Bash et PowerShell natif Windows passent sur 311 fichiers Lean,
  avec un build complet de 313 jobs et aucun avertissement Lean.
- Le balayage exhaustif couvre 26 594 constantes dans 310 modules :
  zéro exception écrite et 364 exceptions générées par Lean. Chaque fichier
  conserve un unique audit final et le scan des termes interdits passe.
- Les 249 modules de production sont accessibles et stratifiés sans
  orphelin. Le nouveau module est H22, la façade H23 ; les droits des autres
  couches sont inchangés. Les 23 fixtures de rejet échouent pour leurs
  diagnostics et sites attendus, sans erreur étrangère.
- Les contrôles documentaires, les références Lean et les 82 liens locaux
  du plan passent. La cible de la section 1 reste inchangée.
  `git diff --check` est propre ; l'avertissement Git LF/CRLF de l'inventaire
  n'est pas un avertissement Lean.
- La comparaison SHA-256 depuis le début du lot montre un ajout, six
  modifications, 400 fichiers inchangés et aucune suppression. Le module
  du lot 39, les quatre fondations, le maître, la machine, les contrats,
  les autres sources de production hors façade, la toolchain, le manifeste,
  le registre et les figures restent inchangés.

Le retour exact et la reprise d'un choix enregistré depuis une intersection
réalisée sont fermés, y compris pour le choix non canonique du client.
La réalisation physique compatible du second volet de R4.2, les lois
physiques R3–R7 et la reconstruction exacte du domaine relativiste restent
ouvertes. Ces lois descriptives ne les remplacent pas. Aucun statut de revue
indépendante n'est modifié, et aucun commit, push, changement de branche
ou audit extérieur n'est effectué dans ce lot.

## 41. Lectures effectivement engendrées par les lois reçues

### 41.1. Obligation examinée avant implementation

Le second volet de R4.2 exige des approximations ayant chacune une réalisation
constitutive compatible. Les fenêtres descriptives des lots précédents ne
produisent pas cette réalisation. Avant d'ajouter une nouvelle loi, déterminer
ce que les rôles du candidat actuel peuvent effectivement produire : émission,
relais avec la calibration reçue, réception, puis différences entre réceptions.
La cible de la section 1 reste inchangée.

Construire une dérivation numérique positive en éliminant les formations
existantes, y compris les comparaisons répétées et leurs suffixes finis de
longueur arbitraire. Elle doit retrouver la racine réellement reçue et les
lectures des ports effectivement utilisés, sans relancer les actions ni
introduire des valeurs indépendantes. Cette dérivation est un diagnostic aval
de lois exécutées, pas un nouveau carrier constitutif, une autre instance maître
ou un moteur physique de remplacement.

Pour une racine de lecture zéro et de calibration un, établir si toute lecture
ainsi produite est entière, puis fermer un séparateur numérique explicite.
Le client doit porter sur tous les suffixes finis du contrat récurrent existant,
pas seulement un programme fixé. Ne pas conclure à partir de mesures ou de
quelques évaluations. Ne pas assimiler valeur numérique, identité d'occurrence
et localisation physique.

### 41.2. Critères et limites

La construction doit être exécutable et ses audits sans axiome. Le raccord à
la racine doit suivre les étapes réellement enregistrées. Les refus, les
inspections, les réceptions positives et les distinctions de parcours restent
ceux du contrat existant ; aucune autorisation n'est modifiée. Vérifier les
clients, la façade, la stratification et les deux gates complètes.

Un obstacle numérique de ce candidat ne réfute ni le cadre, ni la possibilité
de constituer un domaine continu autrement. Il interdit seulement de déclarer
que les lois instrumentales actuelles réalisent déjà toutes les nouvelles
lectures nécessaires. Une telle réalisation demande une construction compatible
supplémentaire ; elle ne peut être remplacée par un raffinement de fenêtres ou
par la réception libre d'une suite numérique.

### 41.3. Construction et résultat fermés

[ProducedReadingLaws](../../RelationalPerimeter/Relativity/Production/ProducedReadingLaws.lean)
retrouve la racine reçue de chaque formation locale, instrumentale ou
récurrente. Pour chaque port typé, son élimination construit une dérivation
numérique positive : lecture reçue, incrément de la calibration reçue,
ou différence de deux lectures produites. Émission et réception transmettent
la dérivation existante ; le relais consomme l'égalité de la calibration du
port avec celle de la racine. Les comparaisons consomment leurs deux références
effectives et les équations de leurs rôles enregistrés.

Cette grammaire numérique donne une loi nécessaire des sorties. Elle ne
prouve pas la réciproque : une dérivation numérique quelconque ne constitue
ni deux réceptions admissibles, ni leur séparation, ni une demande autorisée.
Ces obligations restent dans les formations et constitutions originales.
L'élimination numérique ne remplace pas leurs témoins, leur provenance ni
leurs parcours. Les coefficients entiers ne deviennent pas des identités
d'occurrence.

Le raccord à la racine est prouvé pour chaque étape, puis pour toute histoire
récurrente finie. Il utilise le raccord exact du successeur avec la production
enregistrée. `RecurringRequestedExecution.generatedReading` consomme le
résultat déjà retourné, sans relancer ses demandes. L'entrée de convenance
`recurring_requests_generated_reading` exécute une nouvelle liste reçue une
fois, puis appelle le diagnostic sur son résultat ; elle n'est pas l'entrée
à utiliser lorsqu'on possède déjà ce résultat.

Pour la racine zéro/calibration un, l'élimination de ces dérivations construit
un couple de naturels dont la différence est exactement la lecture. Aucun
résultat de densité ou de localisation physique n'est présupposé.
`generated_unit_reading_gap` prouve que toute telle lecture est au plus zéro
ou au moins un. `generated_unit_reading_between` caractérise les lectures
dans l'intervalle fermé : seuls ses deux endpoints peuvent être atteints.
Le demi est également exclu, par une preuve constructive sur les naturels.

Le client [RecurringInteractionChecks](../../Tests/Relativity/RecurringInteractionChecks.lean)
réemploie ses réceptions positives et ses comparaisons réellement exécutées.
Pour toute liste finie de demandes, inspections et refus compris, il construit
le témoin entier de chaque port de lecture du curseur final et prouve qu'aucun
ne réalise la fenêtre ouverte entre zéro et un. La quantification couvre
aussi les ports nouveaux, pas seulement les anciens ports transportés.
Les deux réceptions sources restent distinctes pour toute cette même liste.
Une lecture du résultat de la deuxième comparaison et une autre du résultat
de session enregistré donnent des témoins exécutables. Leurs évaluations
compilées sont des smoke checks, pas des expériences physiques.

### 41.4. Portée exacte et prochaine obligation

Les lois actuelles de cette racine n'engendrent donc pas des lectures
numériques denses, même avec des reprises finies de longueur arbitraire.
Affiner ses descriptions ne comble pas ce manque. Ce résultat concerne un
canal numérique instrumental : il ne démontre pas que la localisation
physique s'identifie à ce canal, que toutes les racines ont la même lacune,
ou que le cadre ne peut constituer un continu.
La lacune porte sur les champs de lecture du contrat actuel, non sur tous
les lecteurs relationnels qui pourraient être construits depuis ces histoires.

Le second volet de R4.2 reste ouvert. Il faut construire les réalisations
compatibles des contraintes annoncées avec leurs lois constitutives exactes.
Ni le choix d'une autre lecture reçue à chaque précision, sans raccord
constitutif, ni l'ajout libre d'un producteur numérique ne ferme ce passage.
Les primitives n'ont pas été modifiées pour forcer un résultat favorable.
La reconstruction physique R3–R7 et la cible de la section 1 restent ouvertes
et inchangées.

### 41.5. Inspection compilée du diagnostic

Les dix entrées qui consomment les formations ou les résultats enregistrés
atteignent 21 fonctions statiquement nommées. Aucun producteur instrumental,
runner récurrent, chercheur d'échange ni raffineur descriptif n'est accessible
dans cette fermeture. Le helper générique des rôles a trois sites
d'application dynamique du résolveur de dérivations fourni. Dans les entrées
fermées, ce résolveur est construit depuis la formation antérieure ; cette
inspection ne prétend rien sur un callback arbitraire ajouté par un client.

Le code de l'entrée de convenance appelle une fois `runRecurringRequests`
puis une fois l'entrée qui consomme son résultat. Celle-ci projette le curseur
retourné et appelle une fois son diagnostic de lecture. Les preuves de
raccord sont effacées ; les rôles et les dérivations numériques sont des
données exécutables. Le parcours des formations, la construction des
dérivations et le calcul des coefficients ont un coût, non déclaré nul.
Une limite de heartbeats locale à la déclaration de la grammaire numérique
permet son élaboration avec les indices rationnels canoniques ; elle ne
modifie aucune récursion de production, aucun horizon ni aucune gate.

### 41.6. Vérifications du lot

Sur `relativite`, avec Lean 4.33.1 inchangé :

- Le nouveau module a 30 entrées d'audit et le client 38, toutes sans axiome.
  La construction des dérivations et de leurs coefficients compile ; les
  deux lectures fermées du client donnent le couple `(1, 0)`.
- `lake build +RelationalPerimeter` passe avec 251 jobs. Le build complet
  passe avec 314 jobs ; aucun avertissement Lean ni erreur n'est présent.
- Les gates complètes Bash et PowerShell natif Windows passent sur 312 fichiers
  Lean. Leur balayage couvre 26 772 constantes dans 311 modules, avec zéro
  exception écrite et 364 exceptions générées. Les 23 fixtures de rejet
  échouent pour les sites et diagnostics prévus, sans erreur étrangère.
- Les 250 modules de production sont accessibles et stratifiés. Le nouveau
  module est H9, en aval de H8 ; aucun droit de couche existant n'a été modifié
  dans ce lot. Les liens documentaires et références formelles passent.
- Les 84 liens locaux du plan sont valides et sa cible en section 1 est
  identique à celle du commit courant. `git diff --check` est propre ; seul
  Git émet son avertissement LF/CRLF pour l'inventaire.
- La comparaison SHA-256 avec le début de ce lot montre un ajout, quatre
  modifications, 403 fichiers inchangés et aucune suppression. Les quatre
  fondations, les autres modules de production hors façade, les deux nouveaux
  modules des lots précédents, le maître, la machine, les contrats, les scripts
  de contrôle, la toolchain, le manifeste, le registre et les figures sont
  inchangés. Le client des couvertures n'a pas été modifié dans ce lot.

Ce lot ferme la loi numérique et sa lacune pour toute continuation finie du
candidat zéro/un. Il ne ferme pas la réalisation physique du second volet
de R4.2 ni la reconstruction relativiste finale. Aucun statut indépendant
n'est modifié. Aucun commit, push, changement de branche ou audit extérieur
n'est effectué.

## 42. Lecteur relatif sur des parcours effectivement produits

### 42.1. Obligation fixée avant implementation

La lacune de la section 41 ne doit pas être extrapolée à tous les lecteurs
relationnels. Examiner un lecteur instrumental relatif sur deux réceptions
réelles, issues de la même émission constituée, avec des parcours dont chaque
relais consomme la calibration unité. Le parcours de référence doit contenir
positivement au moins un relais. Le lecteur rapporte l'écart effectivement
reçu du premier parcours à l'unité portée par le second ; ses comptes sont
extraits des parcours enregistrés, jamais reçus comme des coordonnées.

Construire une réalisation fermée pour deux longueurs finies arbitraires,
depuis une seule émission, avec conservation des ports, arrivées, parcours
et sources. Le constructeur doit effectuer et partager chaque production
une fois. Le lecteur de résultat ne doit rejouer ni émission, ni relais,
ni réception. Prouver son équation avec les écarts reçus, son transport par
une continuation réelle et ses comptes exacts. Un rapport non entier devra
être réalisé sans changer les lectures brutes ni leurs lois.

Ce lecteur est en aval de la formation et n'est pas une nouvelle primitive
physique. Un rapport de parcours n'est pas encore une localisation. Même
une famille de rapports rationnels réalisés ne ferme pas, à elle seule, la
famille cohérente de localisations du second volet de R4.2. Ne pas remplacer
la cible continue ou relativiste par cette construction instrumentale.

### 42.2. Formation et lecture relative

[RelativePathReadings](../../RelationalPerimeter/Relativity/Production/RelativePathReadings.lean)
définit `UnitJourney` sur un `SignalJourney` réellement enregistré. Chaque
relais consomme le témoin que sa calibration utilisée vaut un. L'émission,
les relais et les étapes intercalaires sont ceux de cette formation exacte.
L'élimination prouve que la lecture finale est la lecture d'émission augmentée
du nombre de ces relais. L'émission commune est une occurrence transportée,
pas une égalité numérique entre deux origines différentes.

`RelativePathReading` reçoit deux contextes de réception positifs et distincts
sur le même support, leurs parcours calibrés, leur émission commune et le
compte positif du parcours de référence. Sa valeur lit effectivement le
premier écart reçu et le nombre de relais du second parcours. Le témoin de
calibration et d'origine commune prouve que ce second compte est exactement
son écart reçu. `measured_ratio_exact` établit que le rapport multiplié par cet
écart réel retrouve le premier écart. Ce n'est ni une cible numérique libre
ni une extension silencieuse du contrat existant.

Le transport consomme une histoire locale enregistrée. Il transporte les
réceptions, les signaux, l'émission, les deux parcours et leurs témoins unité.
La valeur est préservée ; les sources restent distinctes. Les listes complètes
des incréments demeurent dans les records originaux. Le lecteur relatif
n'autorise donc ni regroupement de localisations, ni effacement de mémoire.

### 42.3. Réalisateur fini et continuation effective

[RealizedRelativePaths](../../RelationalPerimeter/Relativity/Production/RealizedRelativePaths.lean)
ferme la réalisation. `runUnitRelays` reprend le curseur produit par son
préfixe et lie une fois chaque résultat de `perform`. Le résultat partagé
fournit le rôle, le successeur, le parcours, sa calibration et l'histoire.
La longueur finie est un paramètre de demandes de production, pas une lecture
fournie ni un temps physique.

`realizeRelativeReading` émet une fois, réalise le premier parcours et sa
réception, puis reprend depuis cette réception pour réaliser le second
parcours à partir de l'émission originale transportée. Sa réception finale
conserve le premier contexte d'arrivée et sa source. Pour tout naturel `p`
et tout naturel `d`, le rapport produit vaut `p / (d + 1)` ; l'histoire contient
exactement `p + (d + 1) + 3` productions. Ces équations sont prouvées sur le
réalisateur, non sur une table de sorties prescrites.

`RelativeReadingExecution.continue` reçoit un résultat déjà produit et un
nouveau programme fini. Il exécute le suffixe depuis son curseur une fois,
compose son histoire et transporte le lecteur enregistré. Il ne relance
aucun parcours antérieur. La valeur et la séparation des réceptions sont
prouvées pour toute telle continuation.

### 42.4. Client public, séparation et portée

[RelativePathChecks](../../Tests/Relativity/RelativePathChecks.lean) importe
uniquement la racine publique. Sa famille part du même candidat zéro/un,
avec son payload reçu, et ferme les constructions pour toutes les longueurs
annoncées. Un parcours unité rapporté à un parcours de deux relais donne le
demi. Un parcours sans relais donne zéro ; les deux lecteurs sont prouvés
différents. Le rapport n'est donc pas un marqueur constant.

Les parcours un/deux et deux/quatre ont le même rapport. Pourtant, une
inspection future permise du record de référence distingue deux incréments
de quatre incréments. Le client prouve leur non-équivalence sous le contrat
local riche : la lecture relative n'identifie ni les émissions, ni les
réceptions, ni leurs effets. Une reprise réelle et des suffixes finis
arbitraires conservent les anciennes réceptions et leurs lectures.

La réalisation du demi ne contredit pas la section 41 : les ports bruts
restent entiers ; c'est un autre lecteur qui rapporte leurs écarts. Le lecteur
est désormais construit sur des réalisations positives, mais ce lot ne
déclare pas ses valeurs des positions ou événements physiques. Il ne prouve
pas encore les raccords d'une famille de localisations à toute précision,
la complétude physique, la métrique ou la reconstruction relativiste. Le
second volet de R4.2 et la cible finale restent ouverts et inchangés.

### 42.5. Contrôle du partage compilé et limites de coût

L'inspection des artefacts C identifie les définitions par leur nom complet
et leur fichier propriétaire. Dans le corps compilé de `runUnitRelays`, le
cas non vide appelle une fois le préfixe récursif et une fois `perform` ; le
résultat de chaque appel est lié avant ses projections. Le corps du
réalisateur appelle deux fois ce runner et trois fois `perform` : une émission
et deux réceptions. Les routes statiquement nommées ne cachent pas d'autre
appel à `perform` hors de ces deux boucles. Le corps de `continue` appelle
une fois le runner du nouveau suffixe et une fois le transport du lecteur,
sans appel au réalisateur initial.

Les lectures d'écart et de rapport atteignent respectivement 23, 23 et 30
fonctions statiquement nommées, sans producteur instrumental ni application
dynamique. Le transport du lecteur atteint 14 fonctions et comporte dix
sites d'application dynamique dans sa fermeture, issus des références de
transport. Le corps du réalisateur comporte quatre applications des
références construites par l'histoire. Ces applications ne sont pas des
callbacks arbitraires fournis au runner. Cette inspection ne prétend pas
auditer un callback inconnu qu'un client ajouterait ailleurs.

Les fractions canoniques utilisent toujours leur recherche numérique
constructive ; elle n'est pas gratuite. Construire, lire et transporter les
parcours et leurs témoins a aussi un coût. La longueur prouvée est un compte
des productions enregistrées, pas un coût physique ou une borne de travail
total. Aucun gain de mémoire minimal ni aucune complexité efficace n'est
revendiqué pour ce lot.

### 42.6. Vérifications locales

Les 15 entrées du lecteur, les 14 entrées du réalisateur et les 17 entrées du
client sont sans axiome. Le smoke compilé du demi retourne son index numérique
et les comptes un/deux ; il ne mesure ni temps physique ni coût total.

La gate complète Bash passe sur 315 fichiers Lean : build de 317 jobs sans
avertissement, balayage de 26 952 constantes dans 314 modules, zéro exception
écrite et 364 exceptions générées. Les 23 fixtures de rejet échouent pour
leurs diagnostics et sites attendus, sans erreur supplémentaire. Le nouveau
client est inclus dans le balayage exhaustif, pas seulement dans les audits
sélectionnés de son fichier. Le build public passe avec 253 jobs.

Les deux modules ajoutés sont H7 puis H8. Aucun droit de couche existant,
aucune primitive ni aucun contrat n'est modifié. La gate comprend les
contrôles documentaires, les références formelles et les contrôles compilés
existants. Les détails du passage PowerShell natif et du contrôle final
d'intégrité sont consignés après leur exécution.

La gate PowerShell natif Windows passe également sur les mêmes 315 fichiers,
avec le même balayage exhaustif et les mêmes 23 rejets attendus. Aucune erreur
ni aucun avertissement Lean n'est présent dans les deux logs. L'inspection
compilée a été réalisée avec une deuxième version du script : la première
arrêtait à tort la racine récursive elle-même au lieu de couper uniquement
son appel récursif. Cette erreur du contrôle a été corrigée dans une nouvelle
version ; le script initial et son échec ont été conservés hors du dépôt.
Aucune source scientifique n'a été adaptée à cet échec.

La comparaison SHA-256 avec le début du lot montre trois ajouts, quatre
modifications, 404 fichiers inchangés et aucune suppression. Les quatre
fondations, les primitives, les formations et contrats anciens, les modules
des lots précédents, le maître, la machine, les autres clients, les scripts
de contrôle, la toolchain, le manifeste, le registre et les figures sont
inchangés. Le contrôleur de constantes est seulement étendu par l'import du
nouveau client et deux commandes d'audit, sans changer ses règles.

La cible de la section 1 et les statuts d'audit indépendant restent inchangés.
Aucun commit, push, changement de branche ni audit extérieur n'est effectué.

## 43. Raffinement productif des parcours relatifs reçus

### 43.1. Obligation fixée avant implementation

Après le lot 42, des fractions sont réalisables séparément, mais leur seule
existence ne construit pas les raccords demandés par R4.2. Le prochain lot
doit repartir du curseur et des deux parcours effectivement reçus. Une
demande locale choisit l'une des deux subdivisions instrumentales : prolonger
le premier parcours de son propre compte, avec éventuellement un relais
supplémentaire, et le second de son propre compte. Les nouvelles réceptions
restent issues de la même émission ; les anciennes sont transportées, jamais
réexécutées ni remplacées.

Le choix de subdivision est une entrée de demande déclarée, pas une décision
physique découverte ni une coordonnée reçue. Les comptes sont lus dans les
parcours positifs enregistrés. Le réalisateur doit partager les résultats
des deux runners et des deux réceptions avant de construire le raccord.
Pour toute liste finie de demandes, conserver l'origine, les références,
les lectures et les effets de parcours des réceptions antérieures.

Prouver ensuite, en aval, le doublement du compte de référence, le raccord
des rapports et l'emboîtement de leurs bornes numériques. Ces bornes servent
au contrôle de précision ; elles ne sont ni des fenêtres ouvertes physiques
ni des points d'espace-temps. Une succession de choix n'est pas la réception
libre d'une suite numérique. Aucun futur achevé ne sera consulté par une tête.
La continuité, les localisations physiques, la couverture et les structures
relativistes restent les obligations séparées de la section 1.

### 43.2. Construction productive et raccord des réalisations

[RefinedRelativePaths](../../RelationalPerimeter/Relativity/Production/RefinedRelativePaths.lean)
reprend un `RelativePathState` constitué : curseur réellement atteint, lecteur
sur ses deux réceptions et calibration unité disponible. La demande `lower`
ou `upper` n'apporte aucun rapport cible. `refineRelativePaths` lit les comptes
des deux parcours, prolonge le premier de son compte avec zéro ou un relais
de plus, le reçoit, puis prolonge le parcours de référence transporté de son
propre compte et le reçoit. Les deux runners et les deux réceptions sont
liés une fois ; leurs sorties servent à leurs rôles, successeurs et histoires.

L'égalité d'origine relie la nouvelle lecture à l'émission antérieure par le
transport de cette histoire exacte. Les deux nouvelles réceptions sont
positivement distinctes. Le lecteur antérieur conserve, sur le support final,
sa valeur, ses deux sources et son record de référence complet. La longueur
de ce nouveau suffixe est le compte antérieur du premier parcours, augmenté
du relais optionnel, plus le compte du second parcours, plus deux réceptions.
Il n'y a pas de nouvelle émission et aucune ancienne production n'est rejouée.

La chaîne positive conserve chaque tête réellement retournée, avec son
raccord exact au réalisateur. `resume` consomme le préfixe déjà reçu ;
`runMore` passe la nouvelle tête à la demande suivante dans l'ordre déclaré.
La composition de deux listes est prouvée comme égalité des résultats
complets. L'ordre des demandes, l'émission commune, les références distinctes
et la valeur du lecteur ancien persistent pour toute longueur finie.
`RelativePathState.prolong` permet aussi de transporter cet état par un
suffixe instrumental ordinaire déjà exécuté avant une nouvelle demande.

### 43.3. Précision en aval, sans la confondre avec une localisation

[RelativePathPrecision](../../RelationalPerimeter/Relativity/Production/RelativePathPrecision.lean)
interprète les comptes réels comme des fractions : si les comptes reçus
étaient `p` et `d`, le nouveau couple est `2*p + b`, `2*d`, avec `b` égal à
zéro ou un selon la demande reçue. Ces nombres sont des lectures de parcours
déjà constitués. Ils ne constituent pas à leur place les parcours ou les
réceptions et ne sont pas utilisés comme identités d'événement.

La borne inférieure est le rapport effectivement lu ; la borne supérieure
est `(p+1)/d`. Leur écart positif vaut `1/d`. Le lot prouve l'emboîtement
des bornes et la division de cet écart par deux à chaque demande, puis ces
lois pour toute chaîne finie. Les choix inférieur et supérieur donnent des
rapports différents sur tout état admis, pas seulement sur un exemple.
Les bornes sont fermées et instrumentales : ce ne sont pas les fenêtres
ouvertes des lots descriptifs, ni des voisinages physiques.
Les deux subdivisions réalisées se rejoignent à leur borne commune et
couvrent exactement l'intervalle rationnel parent. La requête numérique de
ce théorème de couverture n'est une entrée d'aucun de leurs producteurs ;
la preuve ne construit pas un événement depuis cette requête.

Le compte de référence après `m` demandes vaut le compte initial multiplié
par `2^m`. Une borne constructive suffisante pour toute précision rationnelle
positive est prouvée : une liste d'au moins son dénominateur en demandes
suffit pour que l'écart final soit au plus cette précision. Cette borne est
volontairement non optimale ; elle compte des demandes, pas les relais,
opérations, allocations ou durées. Le nombre de relais croît avec le compte
de référence : aucune affirmation d'efficacité ne découle de cette preuve.

`refineToPrecision` ferme aussi cette obligation par un témoin exécutable :
il construit une liste finie de subdivisions inférieures de la longueur
suffisante, lie une seule fois sa reprise du préfixe reçu et retourne cette
réalisation positive avec sa borne prouvée. La liste suffisante n'est donc
pas une hypothèse extérieure laissée ouverte. Ce choix instrumental conserve
la borne inférieure actuelle ; il ne prétend pas choisir une localisation
physique ni établir l'équivalence entre toutes les demandes de subdivisions.

### 43.4. Client et limites conservées

[RelativeRefinementChecks](../../Tests/Relativity/RelativeRefinementChecks.lean)
part du même candidat zéro/un avec payload reçu, réalise d'abord zéro sur
un, puis consomme des demandes de raffinements. Ses preuves couvrent toutes
les listes finies, leur reprise, l'émission et les réceptions anciennes,
les records complets, les bornes et toute précision positive.
La précision possède également un témoin produit sans liste fournie, dont
le raccord exact à la reprise du préfixe est vérifié.
Un suffixe instrumental ordinaire peut être intercalé ; il conserve le lecteur ancien
et les sources de la demande suivante. Le smoke compilé inférieur après
supérieur retourne les comptes deux/quatre et neuf productions nouvelles.
Ce smoke n'est ni une mesure physique ni une expérience de complexité.

Le lot construit donc des réalisations instrumentales successives raccordées,
plutôt qu'une famille de fractions réalisées indépendamment. Il ne ferme
pas encore une présentation idéale avec ses lois de limite, ni la famille
de localisations physiques de R4.2, ni sa couverture ou sa structure
relativiste. Aucun regroupement ou oubli d'effets n'est autorisé par ces
bornes numériques. Les contrats, les primitives et la cible de la section 1
restent inchangés.

### 43.5. Vérification de la réalisation livrée

`lake build +RelationalPerimeter` passe sur 255 jobs. Après ajout du témoin
exécutable de précision, les deux gates complètes passent sur le même état :
`scripts/verify.sh` sous Bash et `scripts/verify.ps1` sous PowerShell natif
Windows. Chacune vérifie 318 fichiers Lean et les 23 fixtures de rejet
attendu ; le build complet couvre 320 jobs. Le balayage porte sur 27 161
constantes de 317 modules : 364 exceptions générées par le compilateur,
aucune déclaration écrite à la main dépendante d'un axiome. Les 254 modules
de production sont tous atteignables, sans orphelin, et leur stratification
est imposée. Aucun avertissement Lean n'est présent. Le message Git sur une
future conversion LF/CRLF de l'inventaire n'est pas un avertissement Lean.

Une inspection bornée du C généré confirme deux appels au runner de relais
et deux nouvelles réceptions dans `refineRelativePaths`, un seul appel à
ce réalisateur dans `resume`, puis un seul appel à `resume` dans chaque
passage de `runMore`. Les lecteurs de l'histoire et des demandes stockées,
le transport d'état `prolong` et les deux lecteurs de bornes ne rejoignent
aucun de ces producteurs dans leur graphe statique. Les appels dynamiques
de transport de références sont recensés ; ce contrôle ne démontre ni un
coût total ni une propriété universelle de tout code appelant.

L'extension de ce contrôle pour `refineToPrecision` vérifie un seul appel à
`runMore`, aucune production directe ni aucun appel dynamique dans cette
entrée. Son corps compilé retourne directement le résultat reçu : la preuve
de borne n'ajoute pas de seconde réalisation. Les scripts d'inspection ont
été figés et hachés avant leurs exécutions, et restent avec leurs logs hors
du dépôt. Ce sont des diagnostics compilés locaux, pas une nouvelle expérience
physique ni un audit indépendant. Les statuts de revue du registre restent
inchangés.

La comparaison SHA-256 avec le début du lot compte trois ajouts, quatre
modifications, 407 fichiers inchangés et aucune suppression. Les quatre
fondations, les contrats et primitives anciens, le maître, la machine, les
lots précédents, la toolchain, le manifeste, le registre et les figures sont
inchangés. L'inventaire est étendu de deux lignes, sans modifier ses règles ;
le balayage de constantes importe le nouveau client sans changer ses règles.
La section 1 reste identique et les 90 liens locaux du plan sont valides.
Aucun commit, push, changement de branche ni audit extérieur n'est effectué.

## 44. Familles productives et présentations idéales instrumentales

### 44.1. Obligation fixée avant implementation

Le lot 43 fournit les raccords entre préfixes effectivement raffinés, pas
encore les lois d'une famille de réalisations à précision arbitraire. Construire
un générateur qui consomme son préfixe stocké et une règle locale déclarée de
subdivision. Sa tête ne reçoit ni indice d'horizon, ni suite numérique libre,
ni futur achevé. Chaque reprise conserve l'émission, les sources et les effets
anciens ; sa composition doit être l'égalité du résultat complet.

Fermer sur ces réalisations le contrôle de Cauchy avec un module de précision
exécutable, puis l'accord numérique entre une famille et sa reprise. Donner
des règles concrètes inférieure, supérieure et alternante, cette dernière
lisant le compte du parcours effectivement reçu. Ce sont des commandes
instrumentales déclarées, pas des lois physiques découvertes.

La famille idéale est une spécification des réalisations finies possibles.
Une requête indépendante de profondeur peut calculer son préfixe depuis la
racine stockée ; elle ne sera pas annoncée comme un lecteur gratuit ni comme
un cache global. La reprise runtime doit, elle, partir du préfixe retourné.
Les limites numériques doivent rester en aval des réceptions et ne seront
jamais des paramètres causaux des producteurs anciens.

Construire aussi les accords avec les bornes pour les règles inférieure et
supérieure, avec module explicite, sans identifier leurs réceptions. Ces lois
d'accord ne peuvent autoriser un regroupement physique ou l'oubli d'un effet.
La classe de règles de ce lot ne couvre pas tous les points du continu :
la couverture, les localisations physiques et la reconstruction relativiste
de R4-R7 demeurent les obligations inchangées de la section 1.

### 44.2. Générateur sur un préfixe reçu

[ProductiveRelativePresentations](../../RelationalPerimeter/Relativity/Production/ProductiveRelativePresentations.lean)
importe la réalisation de précision du lot 43. `RelativePathPresentation`
contient un `RelativeRefinementRun` effectivement formé et une commande de la
grammaire fermée `RelativeRefinementRule`. Il ne contient ni point reçu,
ni suite d'approximations fournie, ni histoire future.

`next` lit la commande sur l'état reçu puis appelle une fois la reprise du
producteur existant. `evolve` passe ce résultat complet à son appel suivant.
Le nombre de pas borne cette récursion finie ; il n'est pas transmis à la
commande locale ou au producteur. `resume` stocke le préfixe effectivement
retourné, et `relative_presentation_resume_exact` prouve l'égalité du résultat
complet entre reprise et exécution composée, pas seulement celle des nombres.

Les commandes inférieure et supérieure demandent les subdivisions déclarées.
La commande alternante lit la parité du compte de relais du numérateur reçu.
Elle ne prétend découvrir une loi physique ni produire une décision
imprévisible. Toutes les profondeurs finies conservent l'émission commune,
les réceptions sources distinctes et les anciens records par le transport
de l'histoire effectivement prolongée. Les deux nouvelles réceptions restent
elles aussi distinctes.

### 44.3. Interprétation numérique et accords construits

`numeric.approximate n` est la lecture relative du préfixe effectivement
produit à profondeur `n`. Les bornes emboîtées du producteur donnent
`relative_evolution_future_close`, puis `relative_evolution_cauchy` pour deux
profondeurs arbitraires assez grandes. Le module explicite est le dénominateur
de la précision rationnelle positive demandée. `realizePrecision` construit
un préfixe et sa preuve de borne sans demander une liste ou une hypothèse de
suffisance extérieure. Ce module est suffisant, pas annoncé optimal.

`resumptionAgreement` construit un accord numérique positif entre la famille
et toute reprise depuis un préfixe retourné. La commande inférieure conserve
la borne inférieure ; la commande supérieure approche la borne supérieure.
Les accords avec ces bornes sont construits avec leurs modules. La commande
supérieure sur la subdivision inférieure et la commande inférieure sur la
subdivision supérieure ont alors un accord à leur frontière numérique commune,
obtenu à partir des comptes des deux subdivisions effectivement réalisées.
Ce n'est ni une égalité des réceptions riches ni une autorisation physique
de regroupement.

[ProductivePresentationChecks](../../Tests/Relativity/ProductivePresentationChecks.lean)
importe seulement l'API publique et ferme les témoins sur le candidat reçu
zéro/un. Il vérifie les raccords complets, les sources et les records, toute
précision positive, Cauchy, la reprise et les accords de frontière. Deux
commandes agissent différemment sur le même préfixe ; la lecture alternante
à profondeur zéro diffère de celle à profondeur un. Il ne s'agit donc pas
d'une suite numérique constante substituée aux lectures produites.
Le smoke exécutable de trois pas retourne les comptes cinq/huit et dix-huit
productions nouvelles. Il n'est pas une mesure physique ou de complexité.

Une demande numérique indépendante peut refaire son préfixe depuis le
préfixe stocké. Seule la reprise explicite conserve le résultat déjà obtenu
pour calculer le suffixe. Aucun cache global ou coût nul de consultation
n'est affirmé. Le parcours de référence double encore par subdivision.

Ces trois commandes construisent des familles idéales instrumentales et
leurs accords. Elles ne caractérisent pas tous les points du continu, ne
ferment pas les localisations physiques de R4.2 et ne reconstruisent pas
la structure relativiste de R4-R7. L'accord numérique reste un readout aval,
pas une identification des sources ou l'oubli d'effets révélables par le
contrat. La cible, les contrats et les fondations restent inchangés.

### 44.4. Vérification de la réalisation livrée

Le build public passe sur 256 jobs. Les gates complètes Bash et PowerShell
natif Windows passent toutes deux : 320 fichiers Lean, build de 322 jobs,
23 fixtures de rejet attendu vérifiées à leur site et pour leur diagnostic.
Aucun avertissement Lean n'est présent. Le balayage exhaustif porte sur
27 254 constantes de 319 modules, avec 364 exceptions générées par le
compilateur et aucune dépendance axiomatique écrite à la main. Les 255
modules de production sont atteignables et leur stratification est imposée,
sans orphelin. Le message Git de conversion future LF/CRLF de l'inventaire
n'est pas un avertissement Lean.

L'inspection locale du C généré résout les définitions par leur nom complet
et leur artifact propriétaire. `next` appelle une fois la commande puis une
fois la reprise existante ; `evolve` appelle cette tête avec deux arguments,
sans horizon. `realize`, `resume` et `realizePrecision` ont chacun un appel
au réalisateur approprié. L'approximation numérique appelle effectivement
`realize` puis lit le chemin produit : une consultation indépendante n'est
donc pas présentée comme gratuite. La commande alternante lit le compte
de relais reçu, tandis que le module de précision n'exécute pas de préfixe.
Aucun appel dynamique n'apparaît dans les huit corps locaux inspectés.
Ce contrôle borné ne constitue ni une borne de coût total, ni une mesure
physique, ni un audit indépendant.

Le script d'inspection a été figé et haché avant le run ; son empreinte
SHA-256 est `F6A0D4B616FF68CC8A40E77A1DF622D606026AA2F5127FAE7D07884F365C2A15`.
Le script et les logs restent hors du dépôt. Les contrôleurs de production
et leurs règles ne sont pas modifiés ; leurs contrôles antérieurs de partage,
de routage et de continuation passent dans les deux gates.

La comparaison avec le début du lot compte deux ajouts, quatre modifications,
410 fichiers inchangés et aucune suppression. Les quatre fondations, les
anciens producteurs, contrats et lecteurs, le maître, la machine, les autres
lots, la toolchain, le manifeste, le registre et les figures sont inchangés.
L'inventaire reçoit une ligne de strate H11 ; le balayage importe le nouveau
client. La section 1 demeure identique et les 92 liens locaux du plan sont
valides. Les statuts de revue du registre restent inchangés. Aucun commit,
push, changement de branche ou audit extérieur n'est effectué dans ce lot.

## 45. Fenêtres ouvertes et recouvrements des familles produites

### 45.1. Obligation fixée avant implementation

Raccorder les fenêtres instrumentales ouvertes existantes aux familles du
lot 44. Un certificat doit contenir le préfixe effectivement réalisé, son
raccord complet au générateur et l'inclusion stricte de tout son intervalle
de précision, pas seulement celle de la valeur à un indice choisi. Les
subdivisions suivantes doivent préserver ce certificat et les anciennes
sources par leurs transports. Construire la restriction, l'intersection
réalisée et les passages positifs dans les deux sens d'une reprise.

Une recherche à budget fini inspectera ces préfixes dans l'ordre et ne
rejouera pas leurs producteurs. Elle devra retourner soit un certificat,
soit le préfixe terminal réellement produit et la preuve que les indices
inspectés ne certifient pas la fenêtre. Cette seconde sortie ne sera pas
présentée comme une impossibilité globale ou la décision d'une comparaison
de réels.

Un recouvrement fini à fenêtres strictement chevauchantes doit sélectionner
une feuille pour toute famille déjà certifiée dans la fenêtre grossière.
Calculer une précision suffisante depuis le chevauchement rationnel,
raffiner depuis le préfixe stocké, puis lire la branche sur ce résultat.
Ne pas fournir la branche, le point limite ou une liste de combinaisons.
La sélection conserve le préfixe produit et sa dérivation de feuille ; sa
restriction retrouve la garantie grossière sur ce même résultat, pas
l'égalité avec un ancien certificat avant les nouvelles productions.

La nouvelle interface reste instrumentale : ses fenêtres ne constituent
pas des voisinages physiques par leur seul nom. L'invariance sous tout
accord numérique entre familles différentes, la couverture du domaine
physique et les obligations relativistes de R4-R7 restent distinctes.
Les contrats, les anciens producteurs et la cible de la section 1 ne sont
pas modifiés. Le lot 44 non commité est préservé.

### 45.2. Certificats sur les productions, restriction et reprise

[ProductivePresentationWindows](../../RelationalPerimeter/Relativity/Production/ProductivePresentationWindows.lean)
consomme les familles du lot 44 et les fenêtres instrumentales existantes.
`ProductiveWindowCertificate` contient une profondeur, le résultat complet
effectivement réalisé, son égalité au préfixe canonique et deux inégalités
strictes encadrant son intervalle fermé. Toute lecture rationnelle entre
ces bornes appartient à la fenêtre ouverte. Toutes les lectures suivantes
de la même famille y restent par l'emboîtement effectivement prouvé.
Un certificat est construit au départ pour toute famille, dans une fenêtre
calculée depuis son intervalle initial et son échelle positive.

`advance` prolonge une fois le résultat reçu. `restrict` conserve ce résultat
et compose les bornes de fenêtres. `common` prolonge le premier résultat
jusqu'à la somme des deux profondeurs et produit un certificat dans
l'intersection. L'autre prolongement sert uniquement à la preuve du raccord
complet et n'est pas une deuxième exécution du producteur dans le runtime.
Les passages `toResumed` et `fromResumed` donnent positivement les deux sens
de l'existence d'un certificat après une reprise arbitraire. Le premier
effectue un suffixe, le second réutilise le résultat reçu. L'équivalence
propositionnelle ne masque pas ces constructions exécutables dans `Type`.

### 45.3. Recherche bornée et recouvrement effectivement sélectionné

`searchProductiveWindowFrom` inspecte d'abord l'intervalle du préfixe reçu.
Lorsqu'il n'est pas certifié et qu'il reste du budget, elle exécute une tête
locale et donne son résultat au suffixe. Au plus `fuel` subdivisions nouvelles
et `fuel + 1` inspections d'intervalles sont autorisées ; ce compte ne mesure
pas les opérations internes des producteurs ou de l'arithmétique.
Le succès porte son certificat et une borne de profondeur construite.
L'épuisement porte le préfixe terminal exact et une preuve d'échec pour
toutes les profondeurs inspectées. `resumeSearch` réutilise ce résultat et
réinspecte son intervalle avant de produire un nouveau suffixe. Aucun échec
fini n'est traduit en impossibilité globale ou comparaison décidée de réels.

Pour une division strictement chevauchante, `strictReadingGap` construit une
précision positive dont la valeur est exactement la différence des coupures.
Sa moitié fournit un budget fini suffisant au producteur existant, sans
hypothèse de suffisance extérieure. `chooseProductive` raffine le préfixe
stocké puis lit la borne supérieure réellement produite. Si cette borne est
strictement sous la coupure supérieure, elle certifie la fenêtre gauche ;
sinon, la borne de précision et le chevauchement certifient la droite.
Les deux sorties portent littéralement le même résultat complet raffiné,
avec la même profondeur. La branche n'est pas une donnée d'entrée.

`InstrumentalReadingCover.selectProductive` consomme structurellement un
recouvrement fini arbitraire et ne parcourt que la branche sélectionnée.
Il retourne sa fenêtre, sa dérivation de feuille et le certificat produit.
`productive_cover_extends_only_its_received_prefix` prouve que le résultat
est un prolongement complet du préfixe reçu, et pas un préfixe reconstruit
depuis l'origine. Sa restriction conserve ce nouveau résultat. Les lectures
ultérieures restent dans la feuille sélectionnée ; les transports de
l'histoire conservent les sources distinctes et les anciens records.
La dérivation de feuille peut conserver le recouvrement fourni au runtime :
aucune minimalité de mémoire ni borne efficace de coût n'est affirmée.

[ProductiveWindowChecks](../../Tests/Relativity/ProductiveWindowChecks.lean)
importe uniquement la racine publique. Il construit le préfixe reçu zéro/un,
les fenêtres et leur chevauchement, puis ferme les certificats des trois
commandes. Il vérifie toute reprise, les raccords complets, toute sélection
finie, les sources et les records conservés. Une seule lecture intérieure
ne suffit pas à certifier un intervalle dont la borne supérieure est exclue.
Le budget zéro échoue ; une production inférieure certifie la même fenêtre.
La recherche peut reprendre après cet échec. La commande supérieure garde
sa borne exclue à toute profondeur finie. Sur le même recouvrement, les
commandes inférieure et supérieure sélectionnent respectivement gauche et
droite depuis leurs résultats effectivement produits. Ces faits finis sont
aussi prouvés par réduction dans le noyau ; le smoke compilé reste seulement
un contrôle d'exécutabilité, pas une mesure physique ou de complexité.

Les fenêtres restent un readout instrumental aval. Ce lot ne les rebaptise
pas voisinages physiques et ne fournit pas la topologie relativiste comme
entrée primitive. L'invariance sous tout accord numérique entre familles
différentes, les localisations physiques et R4-R7 restent à établir. Il ne
modifie ni la cible de la section 1 ni les contrats autorisant le regroupement.

### 45.4. Vérification du lot

Le module et les clients compilent sans axiomes écrits. L'inspection locale
du C généré vérifie les corps nommés, leurs artifacts propriétaires, le
passage du résultat de la tête au suffixe et la reprise du préfixe épuisé.
Le sélecteur comporte un appel au choix et deux sites récursifs alternatifs,
pas deux appels simultanés annoncés comme un. Aucun appel dynamique ni
reconstruction par `realize` n'apparaît dans les sept corps locaux inspectés.
Ce contrôle n'est pas une analyse transitive de coût ou de mémoire.

Le script local V2 a été figé et haché avant exécution ; SHA-256 :
`E23CB40B6CEF3C62F0A2EAE5D7D9B89106DF8889141ADCEBE8FC2C6CC58D5441`.
La première version s'arrêtait à l'import du contrôleur, avant toute
inspection ; elle n'est pas une preuve de réussite. Les scripts et leurs
logs restent hors du dépôt, sans remplacer les contrôleurs de production.

La construction publique finale passe avec 257 jobs. Les deux gates
complètes, Bash et PowerShell natif Windows, passent sur les mêmes 322
fichiers Lean : 324 jobs, aucun avertissement Lean, 23 fixtures rejetées
pour leurs diagnostics et sites attendus. Le balayage complet contrôle
27 450 constantes de 321 modules : 364 exceptions générées, aucune
dépendance axiomatique écrite à la main. Les 256 modules de production
sont accessibles et couverts par l'inventaire, sans module orphelin.
Les contrôles existants de partage, routage, continuation, import et
documentation passent également.

La comparaison avec le début de ce lot compte deux ajouts, quatre
modifications, 412 fichiers inchangés et aucune suppression. Les deux
fichiers propres au lot 44 sont conservés octet pour octet. Les quatre
fondations, les anciens producteurs, contrats et lecteurs, le maître,
la machine, la toolchain, le manifeste, le registre et les figures sont
inchangés. La section 1 reste identique ; les 94 liens locaux du plan
sont valides et le diff ne contient pas de défaut d'espacement. Aucun
commit, push, changement de branche ni audit extérieur n'est effectué.
Ces vérifications ferment le lot instrumental 45, pas les obligations
physiques R4-R7 ni la cible relativiste finale.

## 46. Certification des fenêtres sous accord numérique positif

### 46.1. Obligation fixée avant implementation

Fermer l'invariance laissée ouverte au lot 45 : un accord numérique positif
entre deux familles productives doit permettre de construire un certificat
dans la même fenêtre ouverte sur la seconde famille. Calculer une précision
depuis les deux marges strictes du certificat reçu, consommer le modulus de
l'accord et prolonger le préfixe effectivement stocké de la seconde famille.
La suffisance du budget doit être prouvée, non fournie comme hypothèse.
Le résultat porte le run complet et son raccord exact à cette seconde famille.

Construire les deux directions de l'existence des certificats. Leur accord
numérique ne donne pas l'égalité des préfixes, des occurrences ou des feuilles
choisies par un recouvrement chevauchant. Aucun aller-retour identitaire ne
sera annoncé pour ces certificats : les nouvelles productions restent réelles.
Raccorder le résultat reçu à la sélection de recouvrement sans refaire ce
prolongement. Fermer des clients par les accords déjà construits de reprise
et de frontière commune des deux subdivisions, pas seulement par une interface
conditionnelle sans consommateur.

Ce lot reste instrumental. Il n'autorise aucun regroupement physique ni oubli
mémoire, ne construit pas toutes les localisations de R4.2 et ne ferme pas
R4-R7. La cible de la section 1, les fondations, les contrats, les producteurs
et les contrôleurs existants restent inchangés.

### 46.2. Budget construit et réalisation sur la seconde famille

[ProductiveWindowAgreements](../../RelationalPerimeter/Relativity/Production/ProductiveWindowAgreements.lean)
consomme un certificat déjà réalisé et un accord numérique positif entre
deux familles du lot 44. La précision choisie est la plus petite entre la
moitié de la marge inférieure et le quart de la marge supérieure. Elle est
strictement positive. Les deux marges sont lues depuis l'intervalle complet
stocké dans le certificat, pas depuis une valeur limite fournie.

`certifyAgreed` applique le modulus reçu à cette précision puis ajoute son
dénominateur pour construire un budget suffisant. Son producteur privé,
paramétré par ce budget, reçoit des obligations toutes fermées par l'appelant
public : aucune hypothèse de suffisance n'est laissée ouverte. La comparaison
avec un prolongement du premier certificat intervient dans la preuve.
Seul le préfixe stocké de la seconde famille est prolongé comme donnée ; le
nouveau certificat conserve littéralement le résultat complet de ce producteur.
Le certificat ne transplante pas l'histoire de la première famille.

La preuve combine l'emboîtement du premier intervalle, l'accord des deux
lectures au budget calculé et la précision du second intervalle. Sa borne
inférieure reste strictement au-dessus de celle de la fenêtre ; sa borne
supérieure reste strictement en dessous de l'autre borne. La certification
porte donc sur tout l'intervalle produit, pas seulement sur une lecture.
`productive_window_agreement_iff` ferme les deux directions de l'existence
des certificats, avec des constructeurs exécutables dans `Type`. L'accord
inverse fournit la deuxième construction ; aucune égalité des certificats
ou loi de retour identitaire n'est déduite.

`selectAgreed` donne une fois ce certificat produit au sélecteur de
recouvrement existant. Le résultat est prouvé être un prolongement complet
du préfixe reçu de la seconde famille. Deux familles en accord numérique
peuvent sélectionner des feuilles différentes d'un recouvrement chevauchant.
L'invariance établie concerne l'existence d'un certificat dans une même
fenêtre ouverte, pas l'identité des sources, des histoires ou des feuilles.

### 46.3. Consommateurs construits et frontière du résultat

[ProductiveAgreementChecks](../../Tests/Relativity/ProductiveAgreementChecks.lean)
importe uniquement la racine publique. Il ferme l'interface pour les trois
lois de subdivision et toute reprise finie, avec un certificat complet et
toutes les lectures suivantes conservées dans la fenêtre. Il utilise aussi
l'accord déjà construit entre les deux subdivisions voisines : leurs
lectures initiales sont distinctes, mais leurs certificats d'une même
fenêtre existent dans les deux directions. Le certificat produit sur la
seconde conserve ses sources distinctes et ses anciens records par les
transports de sa propre histoire. Toute sélection de recouvrement repart
de ce préfixe et ne le remplace pas par celui de la première famille.

Le smoke compilé utilise la fenêtre ouverte de moins deux à cinq et une
reprise supérieure d'une étape. Il retourne `(4, 32)` : quatre subdivisions
nouvelles et trente-deux relais dans le parcours de référence retourné.
Ce résultat contrôle seulement l'exécutabilité. Une première évaluation dans
une autre fenêtre, exigeant huit subdivisions, a été interrompue ; elle
n'est pas une mesure ni une preuve de réussite. Les théorèmes génériques,
notamment la quantification sur toute fenêtre, n'ont pas été restreints.

Ce lot ferme l'invariance instrumentale laissée ouverte au lot 45. Il ne
convertit pas l'accord numérique en un regroupement physique ou un oubli
mémoire. Les lois de propagation, les localisations physiques, la couverture
du domaine et R4-R7 restent à construire. Le modulus reçu peut avoir un coût
propre ; le producteur existant double son parcours de référence à chaque
subdivision. Aucune borne efficace de coût, minimalité de mémoire ou nouvelle
validation indépendante n'est annoncée.

### 46.4. Vérifications exécutées et non-régression

Le module et tous les clients publics compilent sans axiomes écrits.
La construction de la racine publique passe avec 258 jobs. Les deux gates
complètes, Bash et PowerShell natif Windows, passent sur les mêmes 324
fichiers Lean : 326 jobs, aucun avertissement Lean, 23 fixtures rejetées pour
leurs diagnostics et sites attendus. Le balayage complet contrôle 27 505
constantes de 323 modules : 364 exceptions générées et aucune dépendance
axiomatique écrite à la main. Les 257 modules de production sont accessibles,
classés et contraints par l'inventaire, sans module orphelin. Les contrôles
existants de partage, routage, continuation, imports et documentation passent.

Un contrôle local du C généré inspecte trois corps propriétaires précisément
nommés. Il vérifie un appel au modulus reçu sur la précision calculée, un
appel au générateur depuis le préfixe stocké de la seconde famille et le
passage de son résultat réel au certificat puis au sélecteur existant.
Les prolongements de la première famille employés dans la preuve sont
absents de ces corps runtime. Le contrôle n'est pas une analyse transitive
du coût du modulus ou des producteurs, ni une minimalité mémoire.

Le script local a été figé et haché avant exécution ; SHA-256 :
`ACD8AE8040EFA109CE23BEA650238467CD95EEECFFF7A5EE3CB3E8037F29E592`.
Sa commande, les empreintes des trois artifacts inspectés et les logs sont
conservés hors du dépôt. Il ne remplace aucun contrôleur de production.

La comparaison avec le début du lot compte deux ajouts, quatre modifications,
414 fichiers inchangés et aucune suppression. Les quatre fondations, les
anciens producteurs, les contrats, le maître, la machine, la toolchain,
le manifeste, le registre et les figures sont conservés octet pour octet.
La section 1 reste inchangée ; les 96 liens locaux du plan sont valides et
le diff ainsi que les deux nouveaux fichiers ne présentent pas de défaut
d'espacement. Aucun commit, push, changement de branche ou audit extérieur
n'est effectué. Le lot instrumental 46 est fermé dans cette portée ;
la cible physique de la section 1 et R4-R7 restent ouvertes et inchangées.

## 47. Reconstruire l'accord depuis les certificats effectivement produits

### 47.1. Obligation fixée avant implémentation

Compléter l'invariance du lot 46 par sa réciproque constructive. Une procédure
qui transforme tout certificat d'une fenêtre de la première famille en un
certificat réalisé de la même fenêtre sur la seconde doit permettre de
construire leur accord numérique et son modulus. La procédure est une donnée
exécutable en `Type`, pas une implication d'existences effacées dont on
extrairait implicitement un choix.

Pour chaque précision positive reçue, produire un préfixe de la première
famille depuis son état stocké, puis former une fenêtre stricte dont le diamètre
est prouvé inférieur ou égal à cette précision. Donner son certificat à la
procédure une fois. Lire les profondeurs des deux résultats pour obtenir une
borne commune. Prouver l'accord de toutes leurs lectures ultérieures depuis
ces certificats, sans donner de queue future au producteur.

Construire les passages dans les deux directions entre accord numérique et
transfert de certificats. Fermer des consommateurs avec les reprises arbitraires
et les subdivisions voisines existantes. Vérifier aussi que les familles
inférieure et supérieure, qui atteignent des bornes numériques différentes,
n'admettent pas ce transfert total. Leurs certificats retournés conservent
les sources distinctes et leurs records.

Ce résultat concerne la complétude des fenêtres pour l'accord numérique des
familles productives actuelles. Il ne prétend ni reconstruire un accord physique
de localisation, ni déduire un transfert de leurs histoires riches, ni autoriser
un oubli. Les fenêtres numériques ne deviennent pas des voisinages physiques.
La cible de la section 1 et les obligations physiques R4-R7 restent inchangées.
Le lot 46 non commité, les anciens producteurs et tous les contrats sont préservés.

### 47.2. Réciproque constructive sur les mêmes familles productives

[ProductiveWindowCompleteness](../../RelationalPerimeter/Relativity/Production/ProductiveWindowCompleteness.lean)
importe le producteur du lot 46. `requestWindow` prolonge réellement l'état
stocké de la première famille au dénominateur de la demi-précision reçue.
Il forme la fenêtre depuis les deux bornes de ce résultat, avec un quart
de précision de chaque côté. La preuve de résolution fournit une borne
de diamètre inférieure ou égale à la précision entière. Les deux marges
strictes et le résultat complet du prolongement sont dans le certificat.
Aucune limite numérique ni queue future n'est une entrée de ce producteur.

`ProductiveWindowTransfer` porte une fonction exécutable : pour toute
fenêtre et tout certificat de la première famille, elle retourne un
certificat réalisé de la seconde dans cette même fenêtre. `compare` produit
une seule requête puis applique une seule fois cette fonction au certificat
réellement reçu. Il conserve la fenêtre et les deux certificats complets.
L'identité réutilise le certificat entier ; la composition donne le résultat
retourné par la première fonction à la seconde.

`toAgreement` construit un accord numérique sans recevoir d'accord
préalable. Pour chaque précision, son modulus est la somme des profondeurs
des deux certificats retournés par `compare`. Toute lecture ultérieure de
chaque famille reste dans la fenêtre certifiée. Deux lectures dans cette
fenêtre de diamètre borné sont donc proches à la précision reçue, même
si leurs indices ultérieurs sont indépendants.

`productive_numeric_agreement_iff_window_transfer` ferme les deux directions
entre l'existence d'un accord numérique et celle d'un tel transfert positif.
La direction accord vers transfert utilise le constructeur du lot 46.
La direction transfert vers accord utilise les profondeurs effectivement
retournées. Les deux constructeurs vivent dans `Type` et compilent.
Ce n'est pas un théorème extrayant une fonction depuis une simple implication
entre existences propositionnelles effacées ; aucun choix de ce genre
n'est utilisé.

Le transfert inverse passe par l'accord reconstruit et son inverse numérique.
Il ne prétend pas retourner le même certificat ou la même histoire riche.
La symétrie de l'accord numérique n'est pas une loi de retour identitaire
des productions.

### 47.3. Consommateurs fermés, séparation et portée

[ProductiveCompletenessChecks](../../Tests/Relativity/ProductiveCompletenessChecks.lean)
importe uniquement la racine publique. Pour toute famille et toute reprise
finie, son transfert prolonge le certificat reçu par le constructeur de
reprise du lot 45. Son nouvel accord est reconstruit depuis ce transfert,
sans fournir l'ancien accord de reprise comme entrée. Les clients prouvent
les préfixes réellement produits, la consommation du certificat reçu,
la formule exacte du modulus et toutes les lectures ultérieures.
Ce modulus vaut deux fois le dénominateur de la demi-précision ; cette
formule ne borne pas le travail des producteurs.

Les subdivisions voisines fournissent un second consommateur, avec l'accord
de frontière du lot 44. Leurs lectures initiales restent distinctes.
Les sources et les anciens records du certificat produit sur la seconde
famille sont conservés par les transports de sa propre histoire.

Le client négatif ferme également un cas non trivial : les familles
inférieure et supérieure issues de l'état reçu construit ont des limites
numériques zéro et un. Un transfert total donnerait un accord entre ces
deux constantes, contredit à la demi-précision unitaire. Le dépôt prouve
donc l'absence de ce transfert ; il ne confond pas des lectures initiales
différentes avec une séparation de limites.

Le smoke compilé reconstruit le modulus du transfert identitaire de la
famille supérieure à la précision unitaire et retourne `4`. Il contrôle
uniquement l'exécutabilité. Une comparaison de constantes dans le client
négatif a d'abord atteint la limite de réduction du compilateur ; la preuve
a été rendue explicite par les deux égalités de valeurs construites.
Aucune limite de réduction n'a été augmentée et cette tentative n'est pas
présentée comme une vérification réussie.

La complétude obtenue est celle des fenêtres pour l'accord numérique de
ces familles générées. Elle n'est ni une égalité des histoires ou des
sources, ni un accord de localisation physique, ni une autorisation de
regroupement ou d'oubli. Les indices futurs interviennent dans les preuves,
pas dans les entrées du producteur. Le modulus exécute sa requête et sa
fonction de transfert lorsqu'il est demandé ; le coût de cette fonction
reste à examiner pour chaque réalisation. Le doublement du parcours par
le producteur existant demeure inchangé. Aucune borne de coût total,
minimalité mémoire ou reconstruction relativiste n'est déduite.
La cible de la section 1 et les obligations physiques R4-R7 restent ouvertes.

### 47.4. Vérifications exécutées et conservation des acquis

Le module et ses clients publics compilent sans axiome écrit. La racine
publique se construit avec 259 jobs. Les gates complètes Bash et PowerShell
natif Windows passent toutes deux sur les mêmes 326 fichiers Lean :
328 jobs et aucun avertissement Lean. Le balayage complet contrôle
27 601 constantes de 325 modules, y compris les déclarations privées :
364 exceptions générées et aucune dépendance axiomatique écrite à la main.
Les 258 modules de production sont accessibles, classés et contraints,
sans module orphelin. Les contrôleurs existants de partage, routage,
continuation, imports et documentation passent, ainsi que les 23 fixtures
rejetées pour leurs diagnostics et sites attendus.

Un contrôle local du C généré vérifie cinq corps propriétaires exactement
nommés. La requête appelle une fois le producteur et conserve son préfixe
réel. La comparaison forme une requête, applique une fois le transfert reçu
et conserve ses deux certificats effectifs. Le modulus appelle une fois
cette comparaison et lit les deux profondeurs réellement retournées.
La composition donne la réponse du premier transfert au second.
La conversion depuis un accord retourne le certificat réellement produit
par le constructeur du lot 46.

Ce contrôle local ne suit pas transitivement le travail de fonctions de
transfert arbitraires. Il ne prouve ni leur coût total, ni une borne physique
de mémoire, ni la génération d'un domaine relativiste. Son script a été
figé et haché avant exécution ; SHA-256 :
`E201E947ABCC81160F9011D3C1CD295F7FDCAF7732B88DBCE435D762F084828F`.
La commande, les empreintes du script et de l'artifact inspecté, les logs
et la comparaison des empreintes sources sont conservés hors du dépôt.

La comparaison avec le début du lot compte deux ajouts, quatre modifications,
416 fichiers inchangés et aucune suppression. Les deux fichiers du lot 46,
les quatre fondations, les anciens producteurs, le maître, les contrats,
la machine, la toolchain, le manifeste, le registre et les figures restent
identiques octet pour octet. La section 1 reste inchangée ; les 98 liens
locaux du plan sont valides. Le diff et les nouveaux fichiers ne présentent
pas de défaut d'espacement.

Aucun commit, push, changement de branche ou audit extérieur n'est effectué.
Le lot instrumental 47 est fermé dans la portée des familles générées
actuelles. Les localisations physiques cohérentes du second volet de R4.2,
leurs lois de propagation et de rencontre, puis la reconstruction R4-R7
restent à construire. L'accord numérique ne remplace aucune de ces obligations.

## 48. Demandes successives de précision depuis les certificats retournés

### 48.1. Obligation fixée avant implémentation

Raccorder les requêtes du lot 47 en une course finie de longueur arbitraire.
Chaque demande reçoit le certificat complet précédemment retourné. Produire
son nouveau préfixe depuis ce résultat, pas depuis l'origine reconstruite.
Former la nouvelle fenêtre en intersectant la contrainte reçue avec la
fenêtre de précision effectivement produite. Les deux conditions devront
être satisfaites par le même intervalle réalisé, pas par deux réalisations
indépendantes déclarées compatibles.

Le résultat de chaque tête porte le certificat dans la famille d'origine,
la restriction à la contrainte précédente, la borne de diamètre demandée,
la profondeur exacte et le prolongement réel du préfixe reçu. La tête
n'a pas de paramètre pour les demandes futures. Le runner donne ensuite
son certificat retourné à la queue et conserve ses productions positives.

Prouver l'emboîtement sur toute course, la formule des profondeurs, l'égalité
au prolongement total pour les données effectivement retournées, l'absence
d'évasion des lectures ultérieures et l'indépendance de la tête envers la
queue. Permettre de prolonger une course déjà produite sans réexécuter ses
producteurs. Fermer des clients depuis la racine publique, notamment sur
des demandes fines puis grossières : la seconde ne doit pas rouvrir la
contrainte précédente.

Ce lot concerne encore les familles instrumentales générées actuelles.
Il ne fournit pas de nouvelle loi physique ni de localisation extérieure,
ne couvre pas toutes les familles d'un domaine relativiste et n'autorise
aucun oubli des sources ou des parcours. Les trois contrôles instrumentaux
existants ne deviennent pas une classe universelle de producteurs physiques.
La cible de la section 1, R4-R7, les lots précédents et les contrats restent
inchangés. Aucun commit, push ou audit extérieur n'est autorisé par ce lot.

### 48.2. Construction depuis le préfixe réellement reçu

[ProductivePrecisionCourses.lean](../../RelationalPerimeter/Relativity/Production/ProductivePrecisionCourses.lean)
importe le producteur du lot 47, sans modifier celui-ci. Le certificat reçu
fournit son préfixe réalisé ; une présentation locale prend ce préfixe comme
entrée et conserve la règle reçue. Une seule requête produit son prolongement
et sa fenêtre. L'intersection avec la contrainte précédente contient les deux
bornes du même intervalle produit. Elle porte donc simultanément l'ancien
engagement et la précision demandée, avec une preuve positive de diamètre.

Le certificat retourné conserve littéralement ce prolongement. Son égalité
à la lecture de la famille d'origine est une preuve de composition, pas un
nouveau calcul depuis cette origine. La profondeur est celle du certificat
reçu augmentée du nombre de subdivisions demandé par la précision.
`ProductivePrecisionContinuation` exige explicitement la restriction à la
fenêtre reçue, le diamètre, cette profondeur et ce prolongement exact.

`runPrecisions` produit une tête puis transmet son certificat à la queue.
La tête n'a aucun paramètre pour les demandes suivantes. La course conserve
les productions réalisées ; son endpoint lit ces enregistrements sans refaire
leurs requêtes. Les preuves portent sur toute liste finie de précisions,
sans longueur maximale : profondeur totale, prolongement composé, restriction
à la fenêtre initiale et maintien de toutes les lectures ultérieures dedans.

`continue` prend l'endpoint déjà retourné et exécute seulement les demandes
supplémentaires. `append` traverse les enregistrements et les listes pour les
raccorder ; il ne rejoue pas leurs producteurs. Ce raccord n'est donc pas
déclaré gratuit, minimal en mémoire ou constant en temps.

### 48.3. Clients publics et portée exacte

[ProductivePrecisionCourseChecks.lean](../../Tests/Relativity/ProductivePrecisionCourseChecks.lean)
importe seulement la racine publique. Les clients ferment les propriétés
pour les trois règles instrumentales et pour toute liste finie de demandes.
Ils conservent les deux références sources distinctes et leurs enregistrements
à travers le transport de l'histoire réellement produite. Deux queues
différentes donnent la même production de tête.

Une demande fine suivie d'une demande grossière reste emboîtée : la seconde
ne rouvre pas la première fenêtre. La course vide retourne le certificat
reçu entier ; une continuation utilise le dernier préfixe retourné. Chaque
fenêtre retournée garde un diamètre strictement positif. L'évaluation de deux
demandes unitaires retourne une profondeur de quatre ; c'est un smoke test
d'exécutabilité, non confirmatoire pour le coût ou pour la physique.

Ce résultat assure une cohérence instrumentale des demandes successives sur
les familles déjà générées. Il ne constitue pas des localisations physiques,
ne déduit pas une règle physique de l'intersection numérique et n'identifie
pas les sources. Le producteur ancien et son double parcours demeurent
inchangés. Aucun coût total, oubli, domaine relativiste ou fermeture de R4-R7
n'est revendiqué.

### 48.4. Vérifications exécutées et conservation des acquis

Le module compile avec 59 jobs, ses clients publics avec 261 jobs et la
racine publique avec 260 jobs. Les gates complètes Bash et PowerShell natif
Windows passent sur les mêmes 328 fichiers Lean : 330 jobs, aucun avertissement
Lean. Le balayage complet contrôle 27 721 constantes de 327 modules,
y compris les déclarations privées : 364 exceptions générées, aucune
dépendance axiomatique écrite à la main. Les 259 modules de production
sont accessibles, classés et contraints, sans orphelin. Les contrôleurs
existants et les 23 fixtures rejetées pour leurs diagnostics et sites
attendus passent.

Le nouveau module est H23 et la racine de relativité H24. Les deux
contrôleurs de stratification reconnaissent maintenant H24 ; la règle
strictement décroissante des imports reste inchangée, comme les autres
strates et frontières. La première gate avait refusé ce rang absent de sa
configuration ; son log est conservé séparément des deux runs réussis.
Les erreurs initiales d'élaboration, corrigées avant ces runs, sont également
conservées ; elles ne sont pas des vérifications réussies. Aucune hypothèse
de preuve ou limite de compilation n'a été relâchée pour les résoudre.

Un contrôle local du C généré vérifie quatre corps propriétaires exactement
nommés. La tête construit sa présentation depuis le préfixe reçu dans les
deux branches d'allocation, appelle une fois la requête et intersecte la
fenêtre réellement retournée avec la contrainte reçue. Le runner transmet
le certificat de cette tête à la queue. La continuation consomme l'endpoint
stocké et exécute une seule course supplémentaire. Le raccord des records
ne contient que sa récursion et celle des listes, aucun appel de producteur
ni callback dans le corps nommé.

Ce contrôle ne borne ni le tas ni le coût total ; il ne supprime pas les
parcours du producteur ancien. Son script a été figé et haché avant sa
première exécution puis réexécuté inchangé après les gates ; SHA-256 :
`5ADA57D6267FFD60856CEDB92AE0748F2F278D7EDFEBD0F75DAA475F4EDEC3BE`.
Les commandes, empreintes, logs et comparaisons sources sont conservés
hors du dépôt.

La comparaison avec le début du lot compte deux ajouts, six modifications,
416 fichiers inchangés et aucune suppression. Les quatre fichiers ajoutés
aux lots 46 et 47, les quatre fondations, les anciens producteurs, le maître,
les contrats, la machine, la toolchain, le manifeste, le registre et les
figures restent identiques octet pour octet. La section 1 est inchangée ;
les 100 liens locaux du plan sont valides. Le diff et les nouveaux fichiers
ne présentent pas de défaut d'espacement.

Aucun commit, push, changement de branche ou audit extérieur n'est effectué.
Le lot instrumental 48 est fermé dans sa portée déclarée. Les localisations
physiques cohérentes du second volet de R4.2, leurs lois de propagation et
de rencontre, puis la reconstruction R4-R7 restent à construire. Les courses
de fenêtres ne se substituent à aucune de ces obligations physiques.

## 49. Raccord de courses depuis deux certificats effectivement retournés

### 49.1. Obligation fixée avant implémentation

Poursuivre le raccord de R4.2 entre réalisations compatibles à toute précision,
dans la portée instrumentale actuellement construite. Le lot 48 prolonge une
famille ; le lot 46 certifie une fenêtre sur une autre famille en accord,
depuis son préfixe stocké. Il manque leur composition successive : chaque
réponse de la seconde famille doit devenir l'entrée de sa réponse suivante.

Recevoir une course déjà produite de la première famille, un certificat de
la seconde dans la même fenêtre initiale et un accord numérique positif.
Chaque tête consomme seulement la production locale enregistrée de la première
et le dernier certificat de la seconde. Construire une présentation depuis
ce dernier préfixe réel ; lui transférer la nouvelle fenêtre en réutilisant
le producteur existant. Revenir à l'indice de la famille d'origine par une
preuve de composition, sans exécuter son origine pour reconstituer le préfixe.

La queue reçoit cette réponse entière. Les fenêtres de toute la course
raccordée sont exactement celles de la course reçue, pas des fenêtres
supplémentaires déclarées compatibles. Prouver la profondeur accumulée,
le prolongement réel, le maintien de toutes les lectures ultérieures dans
la contrainte initiale, l'indépendance de la tête envers la queue et la
possibilité de reprendre depuis les deux endpoints déjà retournés.
Fermer les clients pour des familles voisines dont les lectures initiales
diffèrent mais dont les limites instrumentales ont un accord construit.

L'accord numérique reçu n'est ni un accord de localisation physique ni une
égalité des histoires. Le raccord conserve les références et enregistrements
de chaque source ; il n'autorise aucun regroupement ou oubli. Ne pas appeler
ces familles une couverture du domaine relativiste, ne pas réduire la cible
de la section 1 et ne pas annoncer R4-R7 fermés. Les producteurs anciens,
fondations, contrats, machine, registre et figures restent inchangés.
Aucun commit, push, changement de branche ou audit extérieur n'est autorisé.

### 49.2. Construction et consommation dans l'ordre

[AgreedPrecisionCourses.lean](../../RelationalPerimeter/Relativity/Production/AgreedPrecisionCourses.lean)
importe le lot 48 sans modifier les producteurs précédents. La présentation
locale de la seconde famille stocke littéralement le préfixe de son certificat
reçu. L'accord sur cette présentation garde le module de précision reçu ; sa
preuve replace l'indice local après la profondeur déjà produite. Aucun nouveau
module d'accord, transport d'histoire ou parcours depuis l'origine n'est posé.

Chaque tête appelle une fois `certifyAgreed` sur cette présentation locale et
sur le certificat enregistré de la première tête. `fromReceived` conserve le
résultat réel, ajoute les deux profondeurs et justifie son indice par composition.
Le nombre local de subdivisions est exactement le module de l'accord à la
précision des marges du certificat source, augmenté du dénominateur de cette
précision. C'est un budget de subdivisions, pas une borne du coût total.

`matchAgreed` parcourt la course source déjà produite. Sa tête n'a aucun
paramètre de queue ; la récursion transmet le certificat entier retourné.
Le type de l'endpoint impose exactement la fenêtre de l'endpoint source.
Les preuves couvrent toute liste finie : profondeur accumulée, prolongement
du préfixe réellement reçu, restriction à la fenêtre initiale et maintien
des lectures ultérieures dans celle-ci. `comparison` rapproche les lectures
ultérieures des deux familles lorsqu'une borne du diamètre de cette même
fenêtre est fournie ; ce n'est pas une hypothèse d'égalité des histoires.

`continue` reçoit les deux endpoints déjà enregistrés. Il exécute une seule
course source supplémentaire, puis la raccorde depuis l'endpoint effectif de
la seconde famille. Il retourne ces suffixes, sans rejouer les courses anciennes.
La lecture des records et le module de l'accord reçu ne sont pas déclarés
gratuits ou de coût borné par ces seules preuves.

### 49.3. Clients fermés et limites

[AgreedPrecisionCourseChecks.lean](../../Tests/Relativity/AgreedPrecisionCourseChecks.lean)
importe seulement la racine publique. Deux subdivisions voisines réellement
produites fournissent des familles convergeant vers leur frontière commune,
avec un accord numérique construit. Leurs lectures initiales sont distinctes.
Leurs certificats initiaux dans la fenêtre commune sont construits positivement.

Les clients portent sur toute liste finie de demandes et conservent les
références sources distinctes ainsi que la lecture de leur enregistrement.
Ils vérifient la même fenêtre, les deux continuations depuis les endpoints,
la profondeur réelle, l'indépendance de tête, l'impossibilité de rouvrir une
fenêtre fine par une demande grossière et le diamètre non nul. Pour une demande
de précision, ils ferment aussi le rapprochement de toutes les lectures
ultérieures des deux familles à la précision demandée.

L'unique évaluation ajoutée porte sur la course vide et retourne zéro. C'est
seulement un smoke test d'exécutabilité du cas vide, pas une mesure des courses
non vides. Ni le coût total, ni la localisation physique, ni l'égalité des
sources, ni leur oubli ne sont établis par ce lot. Le raccord instrumental
ne ferme pas les obligations physiques de R4-R7.

### 49.4. Vérifications et conservation des acquis

Le module compile avec 60 jobs, ses clients publics avec 262 jobs et la
racine publique avec 261 jobs. Les gates finales Bash et PowerShell natif
Windows passent sur les mêmes 330 fichiers Lean : 332 jobs, aucun avertissement
Lean. Le balayage complet couvre 27 834 constantes de 329 modules, y compris
les déclarations privées : 364 exceptions générées, aucune dépendance
axiomatique écrite à la main. Les 260 modules de production sont accessibles
et contraints par la stratification, sans orphelin. Les contrôleurs existants
et les 23 fixtures rejetées pour leurs diagnostics et sites attendus passent.

Le nouveau module est H24 et la racine de relativité H25. Les deux contrôleurs
acceptent ces rangs ; leur règle d'import strictement décroissante et les
frontières avec les utilitaires numériques, le maître et la machine ne changent
pas. Les fichiers des lots 46-48 sont conservés sans modification.

Un contrôle du C généré vérifie six corps propriétaires nommés : présentation
depuis le préfixe reçu, conservation du résultat retourné dans les deux branches
d'allocation, tête locale, relais du module de précision, récursion de raccord
et continuation. La tête contient un seul appel au producteur de certificat ;
la queue reçoit le certificat réel de cette tête. La continuation consomme
les deux endpoints enregistrés et appelle une fois chacun des deux producteurs
de suffixe. Le contrôle local du lot 48 passe également, inchangé.

Cette vérification locale ne borne ni le coût interne du module d'accord reçu,
ni le tas, ni le coût total ; elle ne supprime pas les parcours du producteur
ancien. Son script a été figé et haché avant la première exécution, puis
réexécuté inchangé ; SHA-256 :
`390C473FCE1BA1840C9D23E02A816994A940F49A4362BABB701350D72FB05805`.
Les commandes, empreintes, sources et logs sont conservés hors du dépôt.

Les erreurs initiales d'élaboration sont conservées comme diagnostics de
développement, pas comme vérifications réussies. Les preuves ont été réparées
en explicitant les indices et la transparence locale des définitions, sans
affaiblir leurs hypothèses ni augmenter les limites du module de production.
Les clients utilisent explicitement `maxRecDepth 4096`. Le contrôle documentaire
initial a trouvé une ligne blanche superflue en fin du nouveau client ; elle
a été retirée, sans modifier le contrôleur. Les deux gates complètes ont
ensuite été réexécutées sur les sources corrigées.

La comparaison avec le début du lot compte deux ajouts, six modifications,
418 fichiers inchangés et aucune suppression. Les quatre fondations, le
maître, les contrats, la machine, les anciens producteurs, la toolchain,
le manifeste, le registre et les figures restent identiques octet pour octet.
La cible de la section 1 est inchangée. Les 102 liens locaux du plan sont
valides ; le diff et les nouveaux fichiers ne présentent pas de défaut
d'espacement. Les cinq références extérieures n'ont pas été revérifiées.

Aucun commit, push, changement de branche ou audit extérieur n'est effectué.
Le lot 49 fournit le raccord instrumental annoncé, pas les localisations
physiques du second volet de R4.2. Leurs lois de propagation et de rencontre,
puis la reconstruction du domaine et des structures R4-R7 restent à construire.
Ce raccord ne remplace ni ne modifie aucune de ces obligations.

## 50. Composition consommant les certificats intermédiaires produits

### 50.1. Obligation fixée avant implémentation

Poursuivre les lois de composition des raccords de R4.2 dans la portée
instrumentale déjà construite. Le lot 49 produit une course sur une seconde
famille en réponse aux fenêtres enregistrées de la première. Pour une troisième
famille en accord avec la seconde, chaque certificat intermédiaire réellement
retourné doit maintenant fournir les marges et la fenêtre de la réponse suivante.
La composition des seuls accords numériques ne remplace pas cette consommation.

Construire une tête qui reçoit la production intermédiaire enregistrée et le
préfixe réel de la troisième famille. Son budget dépend des marges de ce
certificat intermédiaire et du module de l'accord reçu. Elle retourne son
prolongement réel dans exactement la même fenêtre. La composition parcourt
les records reçus ; elle ne rejoue ni la première ni la seconde course.
Sa queue reçoit le certificat entier que la tête vient de produire.

Prouver la profondeur et le prolongement accumulés, le maintien des lectures
ultérieures dans la contrainte initiale, la tête indépendante des queues et
la possibilité de poursuivre à partir des trois endpoints réellement retournés.
Fermer ces obligations sur les subdivisions voisines existantes et sur une
troisième présentation issue d'un préfixe effectivement prolongé. La course
vide garde le certificat reçu ; les références et enregistrements sources
restent disponibles, sans permission d'oubli.

Les sorties numériques compatibles ne rendent ni les budgets, ni les courses,
ni les histoires des compositions égales. Aucune associativité des exécutions
riches, localisation physique, borne de coût total ou reconstruction R4-R7
n'est annoncée. La cible de la section 1, les fondations, les anciens
producteurs, les contrats, le maître, la machine, le registre et les figures
restent inchangés. Aucun commit, push, changement de branche ou audit extérieur
n'est autorisé par ce lot.

### 50.2. Composition des productions, et non seulement des accords

[ComposedAgreementCourses.lean](../../RelationalPerimeter/Relativity/Production/ComposedAgreementCourses.lean)
importe le lot 49. `receivedCertificate` réindexe à zéro le préfixe réellement
reçu, sans ajouter d'événement. La tête `viaIntermediate` lit le certificat
enregistré de la seconde famille et appelle une fois `certifyAgreed` sur le
préfixe local de la troisième. Le résultat réel revient dans la fenêtre de
la première tête. Le budget de subdivisions lit les marges du certificat
intermédiaire ; ce n'est ni une borne de temps ni une borne de mémoire.

`composeAgreed` parcourt la course première/seconde déjà produite. Chaque
tête consomme sa production intermédiaire, puis transmet son propre certificat
entier à la queue. La première course demeure littéralement l'indice du type
de la course première/troisième ; aucune course source n'est reconstruite pour
la raccorder. La tête locale ne reçoit pas la queue. Les preuves couvrent toute
liste finie, la profondeur accumulée et le prolongement réellement effectué.

`continueComposed` reçoit également la course première/troisième déjà stockée.
Il prolonge la paire première/seconde depuis ses deux endpoints, puis compose
ce nouveau suffixe depuis l'endpoint réel de la troisième. Il ne rappelle pas
`composeAgreed` sur l'ancienne paire pour recréer cet endpoint. Les lectures
de records restent présentes ; aucun coût total ou effacement n'est annoncé.

### 50.3. Clients positifs fermés et portée

[ComposedAgreementCourseChecks.lean](../../Tests/Relativity/ComposedAgreementCourseChecks.lean)
importe seulement la racine publique. Les deux premières familles sont les
subdivisions voisines déjà réalisées ; la troisième présentation provient
d'un préfixe effectivement prolongé de la première, réindexé sans événement
nouveau. L'accord seconde/troisième est construit depuis l'accord voisin et
ce préfixe réel. Pour un prolongement initial d'une étape, la lecture initiale
de la troisième diffère de celle de la première.

Les clients quantifient sur toute liste finie de demandes et tout prolongement
initial. Ils vérifient le budget lu depuis les marges intermédiaires, la même
fenêtre pour toutes les lectures ultérieures des trois familles, les contraintes
initiales, l'indépendance de tête envers les deux queues, les trois reprises
depuis leurs endpoints et la conservation des sources distinctes et de leurs
enregistrements. Le rapprochement première/troisième à une précision demandée
est fermé via le diamètre de cette fenêtre réellement produite.

La seule évaluation est un smoke test de la course vide : il retourne zéro
et ne mesure pas les courses non vides. La composition ne prouve ni l'égalité
des courses obtenues dans différents ordres, ni une associativité des histoires
riches. Les lois de localisation physique, de propagation et de rencontre,
puis la reconstruction R4-R7 restent ouvertes. Ces obligations ne sont pas
remplacées par les accords numériques de ce lot.

### 50.4. Vérifications finales et conservation

Le module compile avec 61 jobs, les clients avec 263 et la racine publique
avec 262. Les deux gates complètes, Bash et PowerShell natif Windows, passent
sur les mêmes 332 fichiers Lean et 334 jobs, sans avertissement Lean. Le
balayage couvre 27 895 constantes de 331 modules, y compris les déclarations
privées : 364 exceptions générées, aucune dépendance axiomatique écrite à la
main. Les 261 modules de production sont accessibles et contraints, sans
orphelin. Les contrôleurs existants et les 23 fixtures rejetées pour leurs
diagnostics et sites attendus passent.

Le nouveau module est H25 et la racine H26. Les contrôleurs acceptent ce rang
supplémentaire sans modifier la règle d'import strictement décroissante ou
ses frontières. La nouvelle preuve cliente du budget a d'abord échoué à
réécrire une définition locale non dépliée ; `dsimp only [composedCourse]`
répare ce raccord sans changer l'énoncé ni les données. Le log de cet échec
est conservé hors du dépôt, et n'est pas présenté comme une vérification passée.

Le contrôle du C généré vérifie quatre corps propriétaires nommés : réindexage
du préfixe, tête intermédiaire, composition et reprise. Il contrôle les
arguments effectifs et les branches d'allocation. La tête appelle un seul
producteur depuis le certificat intermédiaire réel ; le certificat troisième
retourné alimente la queue. La reprise reçoit la course troisième déjà stockée,
lit son endpoint, prolonge la paire une fois et compose seulement ce suffixe.
Les contrôles locaux inchangés des lots 48 et 49 passent également.

Ce contrôle ne borne ni les callbacks internes des modules d'accord, ni le
tas, ni le coût total. Le script a été figé et haché avant son premier run,
puis réexécuté inchangé ; SHA-256 :
`501CB05C0B03DC9BFDBB954B6CB6FF8BCFAC108F2DBA6488475531ED981D8CF1`.
Les commandes, sources, empreintes et logs sont conservés hors du dépôt.

La comparaison avec le début du lot compte deux ajouts, six modifications,
420 fichiers inchangés et aucune suppression. Les fondations, les anciens
producteurs, les huit fichiers ajoutés dans les lots 46-49, le maître, les
contrats, la machine, la toolchain, le manifeste, le registre et les figures
sont identiques octet pour octet. La cible de la section 1 ne change pas.
Les 104 liens locaux du plan sont valides ; les cinq références extérieures
ne sont pas revérifiées. Le diff et les nouveaux fichiers sont propres.

La synthèse de vérification est ajoutée au plan après les gates, sans changer
les sources Lean ou les contrôleurs ; le contrôle documentaire est ensuite
réexécuté. Aucun commit, push, changement de branche ou audit extérieur.
La composition instrumentale est construite ; la localisation physique et
les lois de propagation et de rencontre de R4.2, puis R4-R7, restent ouvertes.

## 51. Reprises conservant les courses et leurs compositions produites

### 51.1. Obligation fixée avant implémentation

Le lot 50 reprend depuis les trois endpoints mais retourne des suffixes.
Raccorder maintenant ces suffixes aux records déjà produits : la course
première/seconde et la course première/troisième doivent conserver leurs
têtes anciennes et recevoir les nouvelles productions, sur la même course
source prolongée. L'ajout de records ne doit appeler aucun producteur.

Construire l'ajout d'une course raccordée depuis son endpoint réel, prouver
le retour complet de l'endpoint du suffixe, l'addition des subdivisions et
la conservation de la tête ancienne. Prouver que composer après cet ajout
donne exactement les mêmes productions que composer l'ancien préfixe puis
son suffixe depuis l'endpoint troisième effectivement retourné. Cette loi
porte sur le même ordre de productions ; elle ne prétend pas permuter les
accords ni rendre leurs histoires associatives.

Construire une reprise commune qui produit une seule fois le suffixe source,
une seule fois sa réponse seconde, puis une seule fois sa composition troisième,
et conserve les deux courses complètes. Fermer les clients sur les familles
voisines existantes et le troisième préfixe réel du lot 50. Conserver les
sources, leurs effets et toutes les lectures futures dans les fenêtres admises.

Les parcours des records et leur copie éventuelle ne sont pas déclarés gratuits.
Les budgets de subdivisions ne sont pas des bornes du coût total. Ce lot ferme
une loi instrumentale de composition des reprises ; il ne remplace pas les
localisations physiques, la propagation, la rencontre ou la reconstruction
R4-R7. La cible, les fondations, les producteurs anciens, les contrats, le
maître, la machine, le registre et les figures restent inchangés. Aucun commit,
push, changement de branche ou audit extérieur n'est autorisé.

### 51.2. Construction positive et loi du raccord

[ResumedAgreementCourses.lean](../../RelationalPerimeter/Relativity/Production/ResumedAgreementCourses.lean)
importe le lot 50. `append` élimine structurellement les records de la course
reçue. Le cas vide retourne le suffixe entier ; chaque pas conserve le head
source et la production seconde déjà enregistrés, puis ajoute seulement les
records suivants. Son calcul parcourt aussi les records source et les listes
de demandes. Il ne rejoue aucun producteur, mais ces parcours ne sont pas
une réduction de mémoire ni une preuve de coût linéaire.

`endpointView` associe la fenêtre effectivement produite à son certificat
entier. La loi de retour compare ce paquet complet à celui du suffixe, pas
uniquement sa lecture numérique. Les subdivisions s'additionnent ; une tête
déjà constituée reste exactement la même production. Le carré de composition
prouve une égalité des courses complètes, sur le même indice source prolongé,
entre la composition de tous les records et l'ajout des deux compositions
successives. Il ne change pas l'ordre des accords ou des événements.

`resumeComposedRetaining` reçoit les deux courses stockées. Il lit l'endpoint
source, produit une fois son suffixe, raccorde une fois le suffixe seconde
depuis son endpoint réel, puis compose une fois le suffixe troisième depuis
son endpoint réel. Les deux ajouts reçoivent ces mêmes productions partagées.
Les deux courses complètes retournées ont littéralement le même indice de
course source prolongée, sans transport ou cast entre elles.

L'élimination par un récursif logique initial n'était pas compilable ; elle
n'a pas été livrée. L'écriture finale utilise des équations à indices explicites
et une récursion structurelle acceptée par le générateur de code. Le carré
conserve son énoncé exact ; ses indices de queue sont explicités par `change`.
Les diagnostics de développement restent hors du dépôt. Aucun construct
interdit ni changement de limite du module de production n'est ajouté.

### 51.3. Clients fermés et limite de portée

[ResumedAgreementCourseChecks.lean](../../Tests/Relativity/ResumedAgreementCourseChecks.lean)
importe seulement la racine publique. Les clients reprennent les subdivisions
voisines effectivement réalisées et le troisième préfixe réel, sur toute
liste finie de demandes anciennes et nouvelles. Ils ferment le carré de
composition sur ces données, les retours complets des deux suffixes, l'addition
des subdivisions anciennes et nouvelles, le prolongement depuis les préfixes
reçus à l'origine, la conservation exacte des deux têtes, les fenêtres futures
et les distinctions et lectures des sources.

L'unique évaluation porte sur deux courses vides et retourne zéro ; elle
n'est pas un run non vide ni une mesure de temps ou de mémoire. Ce lot établit
le raccord des records des reprises instrumentales. Il n'établit ni une
associativité des histoires physiques, ni une permission d'oubli, ni les lois
de localisation, propagation et rencontre ou la reconstruction R4-R7.

### 51.4. Vérifications finales et conservation

Le module compile avec 62 jobs, les clients avec 264 et la racine avec 263.
Les gates complètes Bash et PowerShell 7.6.5 natif Windows passent sur les
mêmes 334 fichiers Lean et 336 jobs, sans avertissement Lean. Le balayage
couvre 27 943 constantes de 333 modules : 364 exceptions générées, aucune
dépendance axiomatique écrite à la main. Les 262 modules de production sont
accessibles et contraints, sans orphelin. Les contrôleurs existants et les
23 fixtures rejetées pour leurs diagnostics et sites attendus passent.
Le module est H26 et la racine H27 ; les frontières et la règle des imports
strictement décroissants restent inchangées.

Le contrôle du C généré porte sur deux corps propriétaires nommés. L'ajout
conserve les champs effectifs des productions anciennes et ne rappelle
aucun producteur. La reprise produit un seul suffixe source, une seule
réponse seconde et une seule composition troisième, puis les transmet aux
deux ajouts. Les arguments, l'ordre des appels et les deux branches
d'allocation sont contrôlés. Le contrôle inchangé du lot 50 passe aussi.
Ces contrôles ne bornent ni les callbacks internes, ni le tas, ni le coût
total ; les parcours et copies de records ne sont pas déclarés gratuits.
Le script a été figé avant son premier run et réexécuté inchangé ; SHA-256 :
`413EFC11AA541C5BCF0C133E5CBEF8A8F537ACF0DA08A46CDB1FB0767443C456`.
Les commandes, empreintes et logs, y compris les diagnostics de développement
échoués, sont conservés hors du dépôt.

La comparaison avec le début du lot compte deux ajouts, six modifications,
422 fichiers inchangés et aucune suppression. Les fondations, les anciens
producteurs, les dix fichiers ajoutés aux lots 46-50, le maître, les contrats,
la machine, la toolchain, le manifeste, le registre et les figures restent
identiques octet pour octet. La cible de la section 1 ne change pas. Les
106 liens locaux du plan sont valides ; les cinq références extérieures ne
sont pas revérifiées. Le diff et les nouveaux fichiers sont propres.

Cette synthèse est ajoutée après les gates sans modifier les sources Lean
ou les contrôleurs ; le contrôle documentaire est ensuite réexécuté.
Aucun commit, push, changement de branche ou audit extérieur. La localisation
physique, la propagation, la rencontre et la reconstruction R4-R7 restent
ouvertes ; les accords numériques de ces courses ne s'y substituent pas.

## 52. Feuilles de recouvrement partagées depuis les endpoints reçus

### 52.1. Obligation fixée avant implémentation

Raccorder les reprises des lots 49-51 aux choix de recouvrement du lot 45.
Une tête reçoit trois certificats sur la même fenêtre et un recouvrement
instrumental justifié. Elle choisit une seule feuille depuis le préfixe
réel de la première famille, puis certifie cette feuille sur la seconde
depuis son endpoint reçu, et sur la troisième depuis son endpoint reçu
en consommant le certificat seconde effectivement produit. Ne pas rappeler
le sélecteur sur les deux autres familles pour choisir une autre feuille.

Construire une course sur toute liste finie de demandes de recouvrement.
Chaque demande reçoit seulement le paquet courant : elle fournit un arbre
de recouvrement autorisé, pas une feuille ni une queue exécutée. La tête
doit être produite avant sa queue, lui transmettre ses trois certificats
entiers, et rester indépendante de la longueur ou des données de cette queue.
Conserver les choix et les productions de chaque tête. Les reprises partent
du paquet effectivement retourné, sans rejouer l'ancienne course.

Fermer les raffinements de fenêtres, les prolongements des trois préfixes
reçus, les retours des reprises et les lectures futures. Raccorder aussi
ces demandes aux endpoints effectivement retournés par les courses du lot 51.
Construire les clients sur les familles voisines déjà réalisées et le
troisième préfixe réel, en conservant les sources et leurs enregistrements.

Ce raccord respecte des recouvrements instrumentaux ; il n'autorise pas un
regroupement physique ni un oubli. Les demandes, leurs arbres et les accords
numériques sont des entrées déclarées. Les générateurs de recouvrement ne
sont pas présentés comme une découverte de lois physiques. La cible de la
section 1, R4-R7, les fondations, les anciens producteurs, les contrats, le
maître, la machine, le registre et les figures restent inchangés. Aucun
commit, push, changement de branche ou audit extérieur n'est autorisé.

### 52.2. Sélection partagée et prolongement effectif

[SharedProductiveCovers.lean](../../RelationalPerimeter/Relativity/Production/SharedProductiveCovers.lean)
importe le lot 51. Le paquet courant garde la fenêtre et les trois certificats
complets. `matchFromReceived` consomme la marge du certificat source, l'accord
positif fourni et la présentation issue du préfixe cible reçu. Le résultat
garde les subdivisions exécutées et la réalisation entière ; ses deux lois
relient sa profondeur et son run au préfixe effectivement reçu.

`selectSharedCover` appelle une fois le sélecteur de la première famille.
Sa feuille et son certificat sont transmis à la réponse seconde ; le certificat
seconde effectivement produit est transmis à la réponse troisième. Le budget
de cette dernière lit donc les marges de cette production intermédiaire,
pas celles d'un certificat recalculé ou du préfixe initial. Les trois résultats
portent la même fenêtre choisie, tout en conservant leurs histoires sources.

`runCovers` est une récursion structurelle sur une liste finie arbitraire.
La demande courante reçoit seulement le paquet courant. Une tête complète
est enregistrée avant la queue, dont le départ est littéralement son endpoint.
Le théorème d'indépendance de la tête compare toutes les queues possibles sur
ce même paquet et cette même demande. Le raccord et le raffinement composent
les prolongements effectifs, sans remplacer leurs runs par des lectures.
`resume` exécute seulement les nouvelles demandes depuis les trois certificats
retournés. Il retourne un suffixe ; il ne prétend pas conserver les anciens
records dans une seule course concaténée. Les parcours des endpoints restent
des calculs, pas des opérations gratuites ni une permission d'oubli.

`coverEndpoint` raccorde les deux courses de précision partageant la même
course source. Il consomme les trois certificats déjà enregistrés dans leurs
endpoints, sans exécuter une nouvelle course ou une nouvelle certification.
Les lois de confinement portent sur toute reprise finie ultérieure des trois
familles. Ce sont des lois instrumentales, pas des lois de propagation physique.

### 52.3. Clients fermés et portée

[SharedProductiveCoverChecks.lean](../../Tests/Relativity/SharedProductiveCoverChecks.lean)
importe seulement la racine publique. Les clients utilisent les deux
subdivisions voisines réellement constituées et un troisième préfixe reçu de
longueur arbitraire. Deux demandes fermées conduisent respectivement à une
feuille gauche et une feuille droite. Leur choix est prouvé depuis les bornes
des brackets produits ; il n'est pas posé dans la demande.

Les clients ferment le prolongement des trois runs, le confinement de leurs
lectures futures, l'indépendance de la tête, le retour du paquet vide, les
reprises successives et le raccord depuis les courses de précision retenues
du lot 51. Les occurrences sources restent distinctes et leurs enregistrements
restent lisibles après transport. L'unique smoke évalué est une course vide,
qui retourne zéro ; ce n'est ni une exécution non vide mesurée, ni une expérience
confirmatoire de coût.

Les arbres, les contrôles des demandes et les accords numériques sont donnés
explicitement. Une feuille choisie sur la première famille n'est pas choisie
à nouveau sur les autres. Ni cet accord ni le choix de fenêtre n'identifie les
sources, n'autorise leur regroupement physique ou leur effacement, ni ne ferme
la localisation, la propagation, la rencontre et la reconstruction R4-R7.

### 52.4. Vérifications finales et conservation

Le module compile avec 63 jobs et ses clients avec 265. Les gates complètes
Bash et PowerShell 7.6.5 natif Windows passent sur les mêmes 336 fichiers
Lean et 338 jobs, sans avertissement Lean. Ces builds sont incrémentaux, pas
des builds depuis `lake clean`. Le balayage couvre 28 106 constantes de 335
modules : 364 exceptions générées, aucune dépendance axiomatique écrite à la
main. Les 263 modules de production sont accessibles et contraints, sans
orphelin. Les 23 fixtures échouent avec leurs diagnostics et sites attendus ;
tous les contrôleurs existants passent. Le module est H27 et la racine H28,
avec les mêmes frontières et les imports strictement décroissants.

Le contrôle du C compilé porte sur cinq corps propriétaires nommés : la
certification depuis le préfixe reçu, la sélection partagée, la course,
sa reprise et le raccord aux endpoints de précision. Il contrôle les appels,
leurs arguments, leur ordre et le stockage des productions effectives.
Le sélecteur source est appelé une fois, les deux certifications successives
une fois chacune ; la troisième reçoit le résultat réel de la seconde.
La queue reçoit le paquet de tête effectivement retourné. Le raccord lit
les records stockés sans rappeler les producteurs ou les certificateurs.
Les callbacks internes, le tas et le coût total ne sont pas couverts par
ces contrôles locaux. Le contrôleur inchangé du lot 51 passe également.

La première version du contrôleur a rejeté à tort les deux stockages du
paquet reçu, l'un dans le cas vide et l'autre dans le cas non vide. Son script
et son log restent conservés. La version 2 a été créée et figée avant son
premier run ; elle exige explicitement ces deux records, leurs tags, leurs
champs et leurs retours. Ses deux runs passent sans modification du script ;
SHA-256 : `F71B07D7729702504077DC2D242A3A8B0EFF3B8DCAF6292F90009CB8B35673CF`.
Les diagnostics de compilation échoués restent aussi conservés. Les deux
cas concrets de feuilles sont finalement fermés par les lois de brackets,
sans augmenter les limites de calcul des preuves ou de la production.

Les gates n'ont modifié aucun des 432 fichiers contrôlés. La comparaison
avec le début du lot compte deux ajouts, six modifications, 424 fichiers
inchangés et aucune suppression. Les fondations, les anciens producteurs,
les douze fichiers ajoutés aux lots 46-51, le maître, la machine, les contrats,
la toolchain, le manifeste, le registre et les figures restent identiques
octet pour octet. La cible de la section 1 ne change pas. Les 108 liens locaux
du plan sont valides ; les cinq références extérieures ne sont pas revérifiées.
Le diff et les nouveaux fichiers sont propres. L'avertissement Git de
conversion LF/CRLF du TSV n'est pas un avertissement Lean.

Cette synthèse est ajoutée après les gates, sans modifier les sources Lean
ou les contrôleurs ; le contrôle documentaire est ensuite réexécuté. Les
scripts figés, commandes, empreintes et logs sont conservés hors du dépôt.
Aucun commit, push, changement de branche ou audit extérieur. Le raccord
instrumental est fermé ; les obligations physiques R4-R7 restent ouvertes.

## 53. Courses de recouvrement conservées lors des reprises

### 53.1. Obligation et périmètre fixés avant l'implémentation

Le lot 52 retourne le suffixe des nouvelles demandes. Le raccord suivant
doit conserver la course reçue entière et lui adjoindre ce suffixe, sans
resélectionner ses feuilles ou refaire ses certifications. Le suffixe doit
commencer littéralement aux trois certificats de l'endpoint enregistré,
pas à des lectures égales ou à des réalisations reconstruites.

Construire un append structurel des records, puis une reprise qui produit
uniquement les nouvelles demandes avant cet append. Prouver l'égalité des
courses complètes entre cette reprise et une course continue sur les mêmes
demandes concaténées, y compris lorsque chaque demande lit le paquet courant.
Prouver aussi le retour de l'endpoint complet, le maintien de l'ancienne tête,
l'ordre des feuilles et des budgets enregistrés, et la conservation des trois
prolongements et des lectures futures. La preuve de l'égalité des courses ne
doit pas se réduire à une égalité de nombres ou de fenêtres.

Réutiliser les fixtures du lot 52 dans les tests, sans nouvelle instance maître
ni import de tests dans la production. Vérifier le C des corps locaux ajoutés :
l'append ne rappelle aucun producteur ; la reprise appelle une fois le runner
du suffixe depuis le paquet enregistré. Ce contrôle local ne constitue pas
une borne de coût, de tas, de callback ou de routage physique. Copier ou
parcourir les records reste du travail.

Les accords positifs et les arbres autorisés restent des entrées déclarées.
Le lot n'établit ni localisation physique, ni regroupement physique, ni oubli
des histoires sources. Il ne ferme pas R4-R7. La cible de la section 1, les
fondations, les modules existants de production, les contrats, le maître,
la machine, le registre et les figures restent inchangés. Aucun commit,
push, changement de branche ou audit extérieur n'est autorisé.

### 53.2. Raccord des productions complètes

[RetainedProductiveCovers.lean](../../RelationalPerimeter/Relativity/Production/RetainedProductiveCovers.lean)
importe uniquement le module du lot 52. `ProductiveCoverCourse.append`
élimine structurellement la course reçue : le cas vide retourne le suffixe,
le cas non vide garde sa tête complète et raccorde sa queue au même suffixe.
L'indice impose le paquet effectivement retourné, avec ses trois certificats
et leurs histoires, comme départ du suffixe. Aucun accord numérique n'est
nécessaire pour cet append de records déjà construits.

Le théorème `productive_cover_run_append_exact` compare les deux courses
complètes, pas leur seule fenêtre ou leur endpoint. L'induction consomme
les mêmes demandes et transmet littéralement le même paquet de tête au
cas suivant. Les demandes peuvent donc lire leurs certificats reçus : la
preuve ne les suppose pas constantes ou déterminées par la longueur.

`resumeRetaining` lit l'endpoint enregistré, produit une course sur les
seules nouvelles demandes, puis raccorde les records. Les lois ferment
l'égalité avec la course continue, le retour de l'endpoint complet, le maintien
de l'ancienne tête et l'ordre des feuilles et des budgets seconde/troisième.
Les reprises répétées ont le même endpoint que les demandes concaténées.
Le réassociement porte seulement sur les listes de demandes ; il ne permute
ni les productions ni leurs histoires. Les prolongements des trois préfixes
et le confinement de toutes leurs lectures ultérieures sont conservés.

### 53.3. Clients, réemploi et frontière scientifique

[RetainedProductiveCoverChecks.lean](../../Tests/Relativity/RetainedProductiveCoverChecks.lean)
importe la racine publique et le client du lot 52 pour réutiliser ses fixtures
fermées, plutôt que reconstruire une autre entrée de production. Aucun module
de production n'importe ces tests. Les clients ferment les lois de courses
entières pour toutes les listes finies de demandes sur ces préfixes, les
deux feuilles gauche/droite déjà prouvées, la conservation de leur ancienne
tête, les reprises répétées et le raccord aux endpoints de précision du lot 51.
Ils conservent les trois paires d'occurrences sources distinctes et la lecture
de l'ancien enregistrement de la troisième source après transport.
Le smoke évalué concerne seulement la reprise vide, pas un coût mesuré.

Un premier build client a signalé un dépassement de calcul pendant
l'inférence d'une application et une dépendance interdite venant du lemme
standard de réassociation des listes. La correction donne explicitement
les arguments du confinement et construit la réassociation par induction
et congruence. Elle n'augmente aucune limite de calcul et ne modifie ni les
énoncés ni les anciens modules. Le log initial reste conservé hors du dépôt.

Ces raccords instrumentaux gardent les contraintes, les productions et les
sources reçues dans leur ordre. Ils ne transforment pas l'accord numérique
en identité des histoires, en autorisation d'oubli ou en localisation physique.
La couverture physique, les localisations, la propagation, les rencontres
et la reconstruction relativiste R4-R7 restent à construire. Le registre
scientifique et les verdicts d'audit antérieurs ne sont pas actualisés par
ces tests locaux.

### 53.4. Vérifications finales et conservation

Le premier build du module passe avec 64 jobs. Le build client corrigé passe
avec 267 jobs. Les deux gates complètes Bash et PowerShell natif Windows
passent sur les mêmes 338 fichiers Lean et 340 jobs, sans avertissement Lean.
Ce sont des builds incrémentaux, pas des builds depuis `lake clean`.
Le balayage exhaustif contrôle 28 151 constantes de 337 modules : 364
exceptions générées, aucune dépendance axiomatique écrite à la main.
Les 264 modules de production sont accessibles, contraints et sans orphelin.
Le nouveau module est H28 et la racine H29 ; les imports restent strictement
décroissants. Les 23 fixtures échouent avec leurs diagnostics et sites attendus.
Tous les contrôleurs existants, y compris ceux du maître et de la machine,
passent. Un client supplémentaire hors du dépôt importe seulement la racine
publique et ferme les lois de course entière et de maintien de la tête,
sans aucun axiome.

Le contrôle figé du C porte sur quatre corps propriétaires : append,
reprise conservant la course, lecture des choix et lecture des budgets.
L'append ne rappelle ni sélection ni certification. Il garde l'ancienne
tête, dans le chemin de réemploi exclusif comme dans le chemin d'allocation.
La reprise appelle une fois la lecture de l'endpoint, une fois le runner des
nouvelles demandes depuis ce résultat et une fois l'append de records,
dans cet ordre. Les lecteurs consomment les feuilles et budgets enregistrés,
sans refaire leurs productions. Le contrôle ne couvre pas les callbacks
transitifs, le tas, le coût total ou une incarnation physique. Son script
version 1 est figé avant son premier run ; SHA-256 :
`8492774BFB9DB4A07124A702E3CBEE67906F08945A6F5FE0E9C693A7C5C9ACBD`.
Le contrôle inchangé du lot 52 passe également sur son C identique.

Les gates ne changent aucun des 434 fichiers contrôlés. Par rapport au début
du lot, il y a deux ajouts, six raccords modifiés, 426 fichiers inchangés et
aucune suppression. Les fondations, tous les anciens producteurs, les lots
46-52 (leurs modules et clients), le maître, la machine, les contrats, la toolchain, le manifeste, le
registre et les figures sont conservés octet pour octet. Le préfixe du plan
allant de la section 1 à la fin de la section 52 est lui aussi inchangé.
Les 110 liens locaux du plan sont valides ; les cinq références extérieures
ne sont pas revérifiées. Le diff et les nouveaux fichiers sont propres ;
l'avertissement Git de conversion LF/CRLF du TSV n'est pas un avertissement Lean.

Cette synthèse est ajoutée après les gates, sans changer les sources Lean
ni les contrôleurs. Le contrôle documentaire est alors relancé. Les scripts
figés, leurs empreintes, commandes, entrées et logs restent hors du dépôt.
Aucun commit, push, changement de branche ni audit extérieur. Le raccord
des courses instrumentales est fermé, pas les obligations physiques R4-R7.

## 54. Entrelacements de précision et de recouvrement sur les mêmes préfixes

### 54.1. Obligation et périmètre fixés avant l'implémentation

Construire une seule course de demandes finies mêlant précision positive et
recouvrement instrumental. Chaque demande reçoit le paquet courant entier,
pas une trajectoire future. Une précision produit d'abord son premier préfixe,
puis la seconde certification consomme ce résultat, puis la troisième consomme
la seconde. Une demande de recouvrement réutilise le producteur du lot 52.
Dans les deux cas, la queue commence littéralement au paquet de tête produit.

Prouver le prolongement des trois histoires et le raffinement des fenêtres.
Toute précision effectivement demandée doit encore borner la fenêtre finale,
même après une précision plus grossière ou une sélection de recouvrement.
Raccorder les records déjà produits et exécuter seulement le nouveau suffixe ;
prouver l'égalité des courses complètes avec l'exécution continue. Convertir
une ancienne course de recouvrement en course mixte sans refaire sa sélection
ou ses certifications, et fermer la spécialisation du runner sur ces demandes.

Les clients doivent réutiliser les trois sources du lot 52 et les endpoints
conservés du lot 53, sans autre maître. Contrôler les appels locaux du C :
une production de précision, deux certifications dans leur ordre, une seule
production de tête par demande et aucune production lors de la conversion
ou de l'append. Ce contrôle ne borne ni les callbacks ni le tas ou le coût
total. Les accords et arbres restent des entrées déclarées. Les histoires
riches restent distinctes ; aucun oubli ou regroupement physique n'est autorisé.

La cible de la section 1, les fondations, les anciens producteurs, le maître,
la machine, les contrats, le manifeste, le registre et les figures restent
inchangés. Ce raccord de R4.1-R4.2 ne ferme ni la couverture physique ni R4-R7.
Aucun commit, push, changement de branche ou audit extérieur.

### 54.2. Un seul runner et des productions complètes conservées

[InterleavedProductiveWindows.lean](../../RelationalPerimeter/Relativity/Production/InterleavedProductiveWindows.lean)
réutilise les producteurs des lots précédents. La tête de précision stocke
sa première continuation et les deux certifications successives ; chacune
prolonge son préfixe reçu. Le type de la troisième certification est indexé
par la seconde réellement produite. La tête de recouvrement réutilise la
sélection partagée du lot 52, sans deuxième sélection.

La tête mixte conserve cette production complète en `Type`, ainsi que son
endpoint et ses lectures enregistrées, avec des égalités exactes. L'opération
est un indice, pas une instruction à recalculer lors de la conversion des
records. La course reçoit seulement le paquet courant, produit la tête, puis
exécute sa queue sur l'endpoint conservé. L'indépendance de la tête envers
l'horizon futur est prouvée pour toutes les demandes et toutes les queues.

La course entière prolonge les trois histoires et raffine sa fenêtre reçue.
`allRequestedBounds` lit les précisions des têtes enregistrées et prouve que
chacune borne encore la fenêtre finale. La preuve consomme le diamètre de
la production correspondante et le raffinement de la queue, pas une fenêtre
finale choisie indépendamment. Les lectures ultérieures des trois préfixes
restent dans la fenêtre initiale. Aucune précision future n'est requise pour
construire une tête présente.

L'append garde les records déjà produits. La reprise exécute le seul suffixe
depuis l'endpoint enregistré ; le résultat complet égale la course continue
sur les demandes concaténées. La conversion des anciennes courses garde
leurs productions et leurs feuilles enregistrées. Sur des demandes uniquement
de recouvrement, les deux runners donnent la même course complète après cette
conversion, et non seulement la même valeur de lecture.

### 54.3. Clients fermés et périmètre des contrôles

[InterleavedProductiveWindowChecks.lean](../../Tests/Relativity/InterleavedProductiveWindowChecks.lean)
réutilise les trois sources et les endpoints de précision conservés du lot 52.
Il ferme les entrelacements précision-recouvrement-précision, les feuilles
gauche et droite lors de la conversion, les reprises de courses entières et
le maintien des trois distinctions sources et de l'ancien signal lisible.
Les énoncés généraux portent sur toutes les listes finies de demandes qui
peuvent consulter leur paquet reçu. Le smoke évalué est vide ; il ne mesure
ni coût ni comportement physique.

La première représentation de la tête conservait son arbre comme donnée :
le C de conversion rappelait alors l'ancienne demande pour reconstruire cet
arbre, bien qu'il ne refît pas la sélection. Cette représentation a été corrigée
avant validation : la production complète reste stockée et ses readouts sont
conservés avec leurs lois de retour, sans requête rejouée par la conversion.
Les premiers diagnostics restent conservés hors du dépôt. Un lemme standard
d'appartenance à une liste concaténée introduisait une dépendance interdite ;
il a été remplacé par une induction constructive, sans augmenter les limites
de calcul ni affaiblir l'énoncé.

Les accords et les arbres autorisés sont toujours reçus. Le raccord ne
construit pas des positions physiques à partir de valeurs, n'identifie pas
les histoires et ne fournit aucune autorisation d'oubli. R4-R7 restent ouverts.
Le registre et les verdicts indépendants ne sont pas actualisés par ce lot.

### 54.4. Vérifications finales et conservation

Le module initial compile avec 65 jobs ; le client final avec 268 jobs.
Les deux gates complètes Bash et PowerShell natif Windows passent sur les
mêmes 340 fichiers Lean et 342 jobs, sans avertissement Lean. Il s'agit de
builds incrémentaux, pas de builds depuis `lake clean`. Le balayage exhaustif
contrôle 28 318 constantes de 339 modules : 364 exceptions générées et aucune
dépendance axiomatique écrite à la main. Les 265 modules de production sont
accessibles, contraints et sans orphelin ; le nouveau module est H29 et la
racine H30, avec imports strictement décroissants. Les 23 fixtures échouent
avec leurs diagnostics et sites attendus. Tous les contrôleurs existants du
maître et de la machine passent. Le client extérieur important uniquement
la racine publique ferme les bornes de précision et l'égalité de la course
complète spécialisée aux recouvrements, sans aucun axiome.

Le contrôleur C version 1 est figé avant son premier run ; ses deux runs
passent sans changement. SHA-256 :
`416945C25DC3329B746E29C3EA5E454D09037FB4985FA13DB9BBC5FBDC6AD59F`.
Il contrôle huit corps propriétaires et le helper de conversion des métadonnées
de demandes. La précision appelle une fois la continuation source puis les
deux certifications dans l'ordre de leurs résultats réels. Le runner appelle
une fois la demande, une fois sa production et transmet l'endpoint conservé
à la queue. L'append conserve la tête complète dans ses deux chemins de
stockage ; la reprise ne produit que le suffixe. La conversion ne rappelle
ni l'ancienne demande ni un producteur, et transmet l'endpoint effectivement
conservé par sa tête. Le contrôle ne couvre pas les callbacks transitifs, le
tas, le coût total ou l'incarnation physique. Les contrôleurs figés des lots
52 et 53 passent eux aussi, avec leurs artefacts C inchangés.

Les gates ne changent aucun des 436 fichiers contrôlés. Par rapport au début
du lot, deux fichiers sont ajoutés, six raccords sont modifiés, 428 fichiers
sont inchangés et aucun n'est supprimé. Les fondations, tous les anciens
producteurs et clients, le maître, la machine, les contrats, la toolchain,
le manifeste, le registre et les figures restent identiques octet pour octet.
Les sections 1-53 du plan sont conservées. Les 112 liens locaux du plan sont
valides ; les cinq références extérieures ne sont pas revérifiées. Le diff
et les nouveaux fichiers sont propres. L'avertissement Git LF/CRLF du TSV
n'est pas un avertissement Lean.

Cette synthèse est ajoutée après les gates, sans modifier les sources Lean
ou les contrôleurs ; les contrôles documentaires sont ensuite relancés.
Les scripts figés, leurs empreintes, commandes, entrées, diagnostics initiaux
et logs restent hors du dépôt. Aucun commit, push, changement de branche
ou audit extérieur. Le raccord instrumental est fermé ; R4-R7 restent ouverts.
