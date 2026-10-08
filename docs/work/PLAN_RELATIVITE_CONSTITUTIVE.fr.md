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
