# Plan d'unification de la fondation et de l'instance maître

Statut : l'audit indépendant du commit `44512e832565b4a2979e44beeab238e5719cf1df`
confirme la cible scientifique (`EXACT TARGET ESTABLISHED`) et demande des
corrections d'unification (`UNIFICATION REQUIRES CORRECTIONS`). Ces corrections
sont implémentées et vérifiées localement : build propre public de 153 jobs,
build complet de 173 jobs, deux vérificateurs sur 171 fichiers Lean et 22 fixtures.
Le sweep couvre désormais 16 938 constantes dans 170 modules importés, sans
dépendance axiomatique écrite à la main ; 360 exceptions générées par Lean sont
identifiées séparément. L'oubli de tout préfixe chronologique n'est pas revendiqué.
G10 reste ouvert : ces corrections n'ont pas reçu de nouveau verdict indépendant.
L'utilisateur a autorisé leur commit, leur push et la relance de l'audit le
4 octobre 2026. Cette publication pour audit n'autorise pas une fusion dans `main`.
Plan initial : 3 octobre 2026. État d'avancement : 4 octobre 2026.

## État effectif du chantier

La cible scientifique citée en section 3 n'est pas modifiée. Les quatre fichiers
fondamentaux sont inchangés. Les ajouts ne remplacent pas la façade publique
auditée par une seconde instance ni par un régime singleton indépendant.

| Lot | État réel |
|---|---|
| G0 | Base figée, build de référence réussi et vérification PowerShell réussie ; le vérificateur Bash de référence échouait sur les retours CRLF du manifeste d'imports. Correction de lecture uniquement, résultat initial conservé hors dépôt. |
| G1 | Correspondances locales et licences examinées. L'examen de faisabilité prouve une obstruction sous conservation exacte des lectures de profondeur et provenance. |
| G2 | Tête réelle produite à travers des références dépendantes typées ; découverte, application, décomposition et assemblage lisent les ressources précédemment produites. Égalité avec la tête publique prouvée. |
| G3 | Regroupement, normalisation, fibres exactes, projections autorisées et raccord aux profils de rôles implémentés. L'image utilise le carrier fini local existant. |
| G4 | Actions sur continuations arbitraires, préservation et cohérence des traces normalisantes implémentées. Le prolongement reçoit désormais l'histoire conservée et son curseur, n'exécute que le suffixe et compose les plongements des profils et obligations. Les références typées sont transportées avec lois de lecture, injectivité, position et composition. |
| G5 | `executeWithReferences` est la récursion unique qui produit l'histoire, le curseur et le transport des ressources. `execute` n'en est qu'une projection. `UnifiedMaster.publicInstance` fournit ce résultat partagé aux consommateurs et fixe son transport au producteur par `referencesExact`. |
| G6 | Moteur vivant concret raccordé aux productions exactes du moteur historique ; contrat fermé pour les requêtes de pas et les lectures des continuations produites. `executeRequests` partage les productions entre événements et successeurs. Les lectures rétrospectives du profil source sont exclues explicitement. |
| G7 | Non-reconstruction du profil réellement normalisé prouvée sur les mêmes rôles publics, avec deux sources distinctes, mémoire commune et mêmes suites futures. Ce résultat ne concerne pas l'oubli du préfixe chronologique canonique. |
| G8 | Le certificat fixe aussi le régime d'image effectif, l'accord de son transport avec `carry`, le curseur terminal de reprise, les lecteurs, l'indépendance des têtes entre horizons, les prolongements et leurs références, l'admission des inspections et la valeur effectivement lue. Le prolongement générique exige un `ProducedPrefix` positif qui fixe le curseur complet à son producteur. Le prolongement conservé est prouvé égal à une exécution ininterrompue. Le certificat scientifique reste séparé de la mémoire runtime. |
| G9 | Builds propres réussis : 153 et 173 jobs, sans avertissement Lean. Les vérificateurs Bash et PowerShell passent sur Windows sur 171 fichiers et 22 fixtures. Les 152 modules de production restent contrôlés, sans orphelin. Le sweep couvre 16 938 constantes, dont les privées, sans dépendance axiomatique écrite à la main. Le contrôle C suit les routes transitives, contrôle `Instance.grow`, `Growth.resume`, la récursion du producteur et exclut l'ancien exécuteur ; il exige les artefacts C de tous les fichiers Lean inventoriés. Le schéma des champs de reprise et de l'état vivant est contrôlé à l'élaboration. Les fichiers protégés et le manifeste restent inchangés. Les rejeux locaux ciblés sont décrits ci-dessous ; ils ne sont pas un nouvel audit indépendant. |
| G10 | Le premier audit est terminé, avec les deux verdicts distincts ci-dessus. Nouvelle validation indépendante des corrections, publication et intégration dans `main` restent ouvertes. Le plan de chantier devra être retiré avant une intégration autorisée. |

### Corrections demandées par l'audit indépendant

La cible scientifique et ses résultats ne sont pas remplacés. Les corrections
ajoutent des accords au certificat, ferment la provenance du prolongement et
renforcent les contrôles de l'implémentation compilée. Elles ne transforment pas
une égalité de valeurs en preuve du nombre physique d'appels : ce dernier point
reste un contrôle statique des interfaces nommées, distinct des théorèmes Lean.

| Rejeu ciblé | Rejet constaté sur la correction |
|---|---|
| M01c : régime `Unit` indépendant | L'accord `Facts.regimeExact` échoue en production. |
| M04d : tête depuis une histoire future complétée | Le graphe compilé révèle l'ancien exécuteur et le rejette. |
| M10 : références depuis un second run caché | Deux routes transitives vers le producteur sont détectées. |
| M11 : rejeu de l'origine dans `Instance.grow` | Les raccords de prolongement et de références du certificat ne typent plus sur l'instance conservée. |
| M14b : suffixe depuis un second ancien exécuteur | L'ancien exécuteur est détecté dans le chemin compilé du prolongement. |
| M15d : archive cachée dans `live` | Le contrôle de schéma rejette le produit contenant la normalisation historique. |
| M18b : événements d'inspection fictifs | La loi de lecture de la sortie produite ne se prouve plus. |
| M18c : admission de toutes les inspections | La caractérisation indépendante de la borne ne se prouve plus. |
| M19b : checkpoint à l'origine, ancien test supprimé | `Facts.restartCursorExact` échoue en production. |

Un client supplémentaire conserve la même frontière et remplace seulement le
support du curseur : son appel au prolongement est rejeté parce que le témoin
`ProducedPrefix` du curseur produit ne porte pas sur ce support étranger.

Ces neuf mutations sont des rejeux locaux ciblés, pas un rejeu des 35 mutations
de l'audit initial. Les adaptations nécessaires à la nouvelle interface positive
de provenance sont enregistrées hors dépôt. Les essais de compilation C sans
le contexte de paquet Lake, ainsi que les patches qui ne s'appliquaient plus,
ne sont pas comptés comme des rejets. Les contrôles de chemins décisifs utilisent
le contexte du paquet et les artefacts compilés des copies isolées.

Les journaux de cette passe sont `correction-clean-public-01.log`,
`correction-verify-ps1-final.log`, `correction-verify-sh-final.log`,
`correction-codegen-final.log` et `correction-docs-01.log`, hors dépôt.
Le manifeste demeure identique après `lake update`. La note de provenance des
reconstructions et les limites du contrôle compilé sont désormais dans les
documents permanents français et anglais, pas seulement dans ce plan temporaire.

### Évidence de fermeture locale

La passe de réparation remplace la reconstruction historique depuis l'origine
par `Instance.grow` puis `Growth.resume`, qui consomment les valeurs conservées.
`growStored` traverse les anciennes têtes sans appeler leur exécuteur. Les
accords d'extrémité portent sur le curseur effectivement retourné et le suffixe
réellement exécuté ; le transport par cette égalité ne prescrit pas une cible
normalisée. Les références restent dans l'interface historique, hors mémoire
de reprise. Leurs lois ne donnent pas un droit de lecture rétrospective ajouté
au contrat futur restreint.

Le sweep échoue sur toute dépendance axiomatique non classée. Ses exceptions
sont distinguées à partir des positions source et des métadonnées des
constructeurs et définitions générées. Le contrôle C est une analyse statique
de l'entrée publique et de ses dépendances nommées ; il n'est ni une preuve de
coût total ni une borne de mémoire physique ou de captures de callbacks arbitraires.

Les journaux versionnés restent hors du dépôt, dans le dossier d'évidence du
chantier. La passe corrigée est enregistrée dans
`reference-repair-clean-public-v1.log`, `reference-repair-clean-full-v1.log`,
`reference-repair-verify-sh-v2.log` et `reference-repair-verify-ps1-v2.log`.
Les versions v1 des vérificateurs ont échoué parce que la fixture d'histoire
étrangère rencontrait un défaut de typage de ses références avant le diagnostic
visé. La fixture reçoit désormais des références correctement typées afin de
tester uniquement le rejet de l'histoire étrangère ; le diagnostic exigé n'est
pas modifié. Les essais antérieurs, réussis ou échoués, restent conservés et
ne sont pas substitués aux résultats de cette passe.

Les deux logs de vérification constatent un seul appel du producteur dans
`publicInstance`, un seul appel pour le suffixe nouveau, aucun appel d'exécuteur
dans `growStored`, et une production partagée entre événement et successeur
dans la reprise. L'examen transitif inclut les fermetures nommées et leurs
initialisateurs. Ces contrôles ne sont pas une borne de coût total.
Les clients `Tests/UnifiedMasterInstance.lean` importent seulement la racine
publique ; leurs audits et les calculs concrets du checkpoint et de la reprise
passent. Les documents permanents bilingues donnent les commandes de reproduction.

### Obstruction précise, et non abandon de la cible

`MasterContinuationFeasibility.PublicPrefix` désigne les préfixes réellement
produits dans l'horizon public. `execute_final_cursor` raccorde leur curseur
à la sortie de la récursion enrichie, et `execute_erases` à l'exécution auditée.
Sur ce domaine, la profondeur vaut `input + elapsed` et la longueur de la
provenance vaut `elapsed`.

`PreservesDiscoveryReads` fixe explicitement les deux lectures exactes conservées.
`coordinates_exact` reconstruit alors le couple `(input, elapsed)` depuis la seule
mémoire. `projection_injective` prouve que cette mémoire distingue tous les
préfixes publics. `no_historical_separator` en déduit que deux mémoires égales
ne peuvent différer pour aucune observation historique de ce domaine.

La reconstruction est également une donnée exécutable, pas seulement une
injectivité propositionnelle : `PreservesDiscoveryReads.decode` vérifie l'horizon
et retourne le préfixe. `decode_exact` prouve sa loi de retour sur toute mémoire
projetée. `recoverRead_exact` permet ensuite de reconstruire chaque lecture
historique, notamment le curseur réellement produit, sans recevoir le préfixe
source comme argument du décodeur. Aucun coût de reconstruction n'est borné ici.

Cela interdit le séparateur de G7 sous CE contrat. Cela ne démontre ni une
impossibilité de tout oubli sous un contrat plus faible, ni une borne de mémoire,
ni un défaut du phénomène computationnel précédemment audité.

### Rectification du diagnostic et contrat réalisé

L'exigence de reconstruction de la liste complète était mon choix de contrat,
pas une nécessité générale démontrée. Elle ne devait pas être utilisée pour
conclure à l'impossibilité du chantier. La relecture a aussi distingué deux
domaines : les préfixes chronologiques de la recherche, et les parcours réellement
exécutés de normalisation de ses profils constitués.

Le nouveau lot ne change ni la cible de section 3, ni la famille publique.
Il utilise les profils distincts et leur convergence déjà produits par cette
instance. `ProducedProfileContinuation.publicExecution` fournit à la fois
l'histoire dont provient la normalisation et le curseur de reprise. Le moteur
vivant conserve la provenance dont la découverte a encore besoin ; il ne stocke
ni support de ressources ni préfixe opérationnel. La mémoire du checkpoint
conserve la sortie réellement normalisée et les lecteurs issus de cette sortie,
mais pas le profil source ni son résultat historique de normalisation.

Le contrat autorise toute suite finie de requêtes : avancer de plusieurs pas
dans la vraie recherche, ou lire une variable d'une continuation produite à un
rôle existant. Les bornes des rôles sont vérifiées par l'admission. Le moteur
public étant paramétré par un nombre de pas, ce contrat ne prétend pas inventer
une interface interactive plus générale. Les événements de découverte, application
et décomposition et les lectures vivantes sont préservés exactement.

Deux normalisations concrètes des profils publics gauche et droit donnent la
même mémoire. Leur distinction d'origine n'est pas décodable, et toutes les
requêtes du contrat donnent les mêmes événements futurs. Ceci ferme l'oubli
du profil source normalisé, et non l'oubli de toute provenance ou de tout préfixe
chronologique. Les lectures historiques complètes restent dans leur API séparée.
Une borne de mémoire ou de temps n'est pas déduite de ce résultat.

### Correction finale du plan, avant fermeture de la façade

L'ancienne rédaction du lot 7 exigeait deux préfixes chronologiques alors que
la donnée effectivement candidate à l'oubli est ici le profil consommé par la
normalisation. Le domaine fixé est désormais celui des résultats de cette
normalisation exécutée. Ce choix est nommé dans le contrat et dans les preuves ;
il ne vaut pas preuve de perte de la provenance chronologique.

L'ancienne ligne G5 suggérait aussi de remplacer toutes les déclarations
publiques. Ce n'est ni nécessaire à une seule chaîne de production, ni compatible
avec l'exigence de conserver l'API auditée. La nouvelle façade doit recevoir le
résultat de l'exécuteur par ressources, en dériver ses rôles, sa normalisation,
ses régimes et sa mémoire, puis prouver le raccord aux anciens résultats.
Le moteur de référence n'est pas appelé en parallèle. Les nouveaux consommateurs
de la façade utilisent ces projections communes, pas des constructions étrangères.

La fermeture locale comprend code, clients, documentation bilingue et contrôles.
L'audit externe et la publication forment un lot séparé soumis aux autorisations
explicites de la section 16. Ils ne seront pas déclarés exécutés ici.

La reprise doit aussi partager chaque production entre son événement et son
successeur. L'interface runtime est `ProducedContinuation.executeRequests` ;
elle utilise `LiveContinuation.execute`, qui renvoie les deux résultats dans
une seule récursion. Les fonctions séparées d'événements et de successeurs
restent les spécifications du contrat, non un protocole runtime à deux passages.
Les preuves `executeRequests_next` et `executeRequests_events` ferment leur
accord pour toutes les suites finies. Le transport d'image vers les obligations
produites possède les deux retours et l'accord de `carry` ; il n'est ni un
décodeur de profils sources ni l'inverse des actions sur données arbitraires.

## 1. Projet cible, branche et références figées

Le seul projet publié à l'issue de ce chantier est `relational-perimeter`.
Le travail est effectué sur `codex/unified-foundation-master-instance`, dans
un worktree indépendant. Aucune autre branche de travail n'est déplacée.

Base de départ : `4e0febf032821882069e7cfefd7e631fc8461d95`, résultat ayant reçu
le verdict indépendant `EXACT TARGET ESTABLISHED`.

Matériau comparé : `c98864b4a2d806581c87770d28d8c47768480e12`, branche
`codex/certified-grouping` de `relational-foundations`. Ce dépôt informe la
reconstruction locale ; il ne devient pas une dépendance du projet cible.

Le worktree plus récent, ses modifications non commitées, ses expériences et
ses branches ne constituent pas une autre base implicite. Toute reprise de
matériau supplémentaire doit être identifiée avant incorporation.

Les archives, rapports comparatifs, scripts d'audit et fragments sources bruts
restent hors du dépôt. Le présent document est temporaire et doit disparaître
de l'arbre proposé à `main` ; les preuves, instructions de reproduction et
documents scientifiques canoniques constituent les livrables permanents.

## 2. Objectif du chantier

Conserver intégralement le phénomène computationnel audité, le raccorder à une
théorie locale générale de regroupement certifié, puis construire sur la même
instance maître les garanties de ressources typées et de continuation réduite
qui sont aujourd'hui établies sur une autre instance.

« Une seule instance maître » signifie une chaîne effectivement commune de
production, avec les mêmes états produits, rôles, occurrences, actions et
consommateurs. Deux programmes indépendants placés dans un couple ne satisfont
pas cet objectif. Une interface générique commune ne le satisfait pas non plus
si ses réalisations concrètes restent sans raccord.

Le chantier ne vise ni une solution de SAT arbitraire en temps polynomial,
ni une borne de coût total nouvelle, ni une supériorité logique sur Lean,
ni une conclusion universelle sur toutes les formes d'exponentielle.

## 3. Cible scientifique à préserver, sans substitution

> Dans ce cadre, la constitution relationnelle des dépendances est primitive. Le calcul produit lui-même, pendant son exécution et à partir de ce qu'il a déjà produit, sa décomposition opérationnelle et détermine ainsi quelles alternatives doivent continuer à être traitées comme des obligations indépendantes.
>
> Cette exécution ne produit pas d'explosion exponentielle de la largeur opérationnelle : bien que le déploiement extensif des profils constitués ait une largeur 2^n, le régime exécuté les regroupe en une seule obligation sans identifier les profils eux-mêmes.
>
> Dans la classe binaire formalisée, une largeur opérationnelle exponentielle apparaît si et seulement si le régime impose de conserver séparément toute la multiplicité extensive, c'est-à-dire si son application carry est injective.
>
> L'explosion exponentielle de la largeur opérationnelle est donc démontrée ici comme l'effet exact de cette exigence extensive de conservation indépendante, et non comme une conséquence nécessaire de la structure relationnelle du problème elle-même.

Le théorème exact à maintenir caractérise l'égalité à la largeur intégrale
`2^stageCount` pour les régimes surjectifs de la classe. Il ne caractérise pas
toute croissance exponentielle : une largeur partielle `2^k`, avec `k < n`,
peut rester exponentielle lorsque `k` croît avec `n`.
Dans la réalisation publique, `n = input + 1` est le nombre de rôles exécutés ;
`k` est le nombre de rôles dont les alternatives restent séparément portées.
Ces paramètres ne sont pas interchangeables avec la profondeur initiale.

L'extensivité demeure une lecture quantitative. Elle n'est pas une couche
constitutive nouvelle, ni une source de rôles. Les identités sources demeurent
distinctes lorsque leurs obligations sont regroupées.

Les gains du nouveau regroupement doivent être nommés correctement : le résultat
`2^pendingCount` existait déjà dans la base. Les apports supplémentaires recherchés
sont les raccords locaux, la cohérence des actions de toutes les traces et les
lois de prolongement, pas la redécouverte de cette cardinalité.

Dans la base, les politiques mixtes sont des comparaisons autorisées sur une
histoire de rôles constituée, non d'autres exécutions de la recherche publique.
Le résultat `2^k` doit conserver cette portée. Si une production exécutée de
partitions mixtes est recherchée ensuite, elle exige sa propre construction ;
le choix extérieur d'un masque ne sera pas présenté comme une découverte.

L'équivalence générale entre pleine largeur et injectivité est le composant
de dénombrement du résultat. Les relations ne sont pas nécessaires à sa preuve
cardinale, et leur trivialisation dans une famille générique n'est pas réfutée
par ce lemme. La consommation des relations, de l'action et de la préservation
doit être établie dans la constitution et l'exécution concrètes, sans fabriquer
une dépendance de ce lemme à des témoins qu'il ne requiert pas.

## 4. Invariants architecturaux non négociables

1. Les quatre fichiers `SegmentedResidualRole.lean`,
   `AbstractSegmentedTurning.lean`, `ExactTypeTransport.lean` et
   `StrongPerimetralTurning.lean` restent l'autorité initiale. Leur contenu est
conservé octet par octet pendant les premiers lots. Aucun dossier `Foundation`
   concurrent et aucune couche `Alignment` ne sont introduits.
2. Les familles relationnelles, leur orientation, leurs indices et leurs témoins
   dans `Type` sont explicités avant les occurrences qui les réalisent.
3. Formation, source, cible, provenance et composabilité ne sont pas remplacées
   par une étiquette numérique ou par des champs sans rôle dans les constructions.
4. Le carrier scientifique des profils provient de l'histoire dépendante de
   rôles. Une représentation binaire n'intervient qu'après cette constitution,
   avec ses lois de retour et les accords relationnels nécessaires.
5. La découverte, l'action et la décomposition de tête sont produites dans la
   récursion d'exécution avant la récursion sur la suite. Le prochain état est
   celui réellement produit par la tête ; aucun futur complété ne la détermine.
6. L'action sur des continuations arbitraires et sa preuve de préservation sont
   distinctes. Aucune des deux n'est remplacée par le fait que les cibles coïncident.
7. La normalisation produit son résultat et sa trace ; elle ne reçoit pas une
   cible imposée dont la justification serait retrouvée après coup.
8. Le régime est l'image exacte des sorties produites. Son `carry` ne fusionne
   pas de cibles distinctes et ne sépare pas deux cibles identiques.
9. Le carrier de classe et le carrier exécuté restent définitionnellement le
   même au point d'application du `iff`, sans adaptateur caché.
10. Un transport exact réversible de porteurs, un transport dirigé préservant
    l'acceptation et un contrat de continuation exacte restent trois interfaces
    différentes. La conservation d'une relation n'est pas déduite d'une bijection.
11. Une donnée historiquement constituée peut être absente de la mémoire future
    sans que son identité soit niée. Mais cette absence exige un contrat futur
    explicite et une preuve ; elle ne découle pas de la largeur un.
12. Un théorème conditionnel décrit honnêtement une interface. Chaque propriété
    annoncée pour l'instance maître doit avoir ses hypothèses effectivement fermées.

Chaque consommateur doit indiquer quelle détermination il reçoit, de quel
producteur, par quel transport, et avec quelles lois. Une égalité terminale
seule ne remplace pas cette chaîne.

## 5. Architecture locale envisagée

Les emplacements suivants sont des destinations de modules à construire, et
non des fichiers existants annoncés comme déjà fonctionnels.

```text
SegmentedResidualRole.lean
AbstractSegmentedTurning.lean
ExactTypeTransport.lean
StrongPerimetralTurning.lean
RelationalPerimeter.lean
RelationalPerimeter/
  Constitution/
    Resources/
      TypedReferences.lean
      ConstructedSupport.lean
    Grouping/
      Traces.lean
      Rules.lean
      Normalization.lean
      Projections.lean
      Reindexing.lean
      ExactImage.lean
      BinaryReadout.lean
      ContinuationContract.lean
      HistoricalExtension.lean
  Computation/ConstitutiveSearch/EndogenousDecomposition/
    ... modules audités existants ...
    CertifiedRoleGrouping.lean
    RoleGroupingSemantics.lean
    HistoricalRoleGrouping.lean
    MasterResourceExecution.lean
    MasterContinuationFeasibility.lean
    LiveResourceContinuation.lean
    ProducedProfileContinuation.lean
    UnifiedPublicCertificate.lean
Tests/
  ... régressions auditées existantes ...
  UnifiedConstitution.lean
  ProducedContinuation.lean
  UnifiedMasterInstance.lean
scripts/
  ... vérificateurs et inventaires étendus ...
docs/
  ... documentation scientifique française et anglaise ...
```

Les modules `Constitution` sont des constructions dérivées des interfaces locales,
pas une nouvelle fondation placée au-dessus des quatre fichiers initiaux.
Les noms doivent être rapprochés des modules déjà présents avant création pour
éviter les doublons. L'histoire primitive existante doit être réemployée ; une
trace opérationnelle distincte doit avoir ses indices et son raccord explicites,
et ne pas devenir une seconde histoire primitive concurrente.

La structure physique des fichiers ne prouve pas cette stratification. Un
inventaire complet des imports et les dépendances des termes décisifs doivent
la confirmer. Aucun stratum accueillant le certificat final ne reste sans règles.

### Intégration au paquet dès la création des modules

Le `lakefile.toml` de la base couvre `RelationalPerimeter.Computation.+`, mais
pas le nouveau chemin `RelationalPerimeter.Constitution.+`. Étendre explicitement
les globs, l'inventaire de stratification et les vérificateurs avant de livrer
un module à cet emplacement. Exposer les résultats scientifiques depuis la
racine publique, sans cycle d'import et sans rendre cette couche générique
dépendante de la façade finale de l'instance.

Chaque lot doit être compilé et audité au moment de sa livraison. G9 est une
validation globale, pas le premier moment où ses fichiers sont vérifiés.

## 6. Lot 0 — Figer la référence et le registre de conservation

### Actions

- Relever le commit de base, les hashes des sources/configurations, le toolchain,
  les déclarations publiques et les consommateurs décisifs dans un dossier extérieur.
- Conserver les résultats de l'audit indépendant comme référence, sans les écraser.
- Reproduire les builds, les deux vérificateurs disponibles et les audits sur
  une copie indépendante ; consigner toute commande qui ne peut pas être exécutée.
- Répertorier les théorèmes de largeur, de distinction, de fibres exactes,
  de préservation, de localité et d'effacement de l'exécution enrichie.
- Fixer le périmètre des connaissances transférées et vérifier les licences
  et notices des matériaux concernés. Conserver la licence du projet cible.

### Livraison et gate G0

Registre extérieur : pour chaque garantie ancienne, déclaration, type, producteur,
consommateurs, probe client et commande de vérification. Les quatre fichiers
initiaux ont leurs hashes protégés. Aucun changement scientifique n'est accepté
avant que la référence soit reproductible.

## 7. Lot 1 — Cartographie de la fondation commune

### Actions

Construire une table de correspondance pour :

| Objet | Question à fermer |
|---|---|
| Relations et nœuds | Quelles familles et quels témoins constituent réellement le nœud ? |
| Histoires et occurrences | Quelle histoire fait autorité ? Quelles sources/cibles composent ? |
| Quantité exacte | Quels transports réalisent les positions avant la lecture numérique ? |
| Ressources typées | Quelle occurrence a produit une ressource et à quelle sorte appartient-elle ? |
| Références | Quelle ressource est lue, avec quelle identité et quelle provenance ? |
| Actions et obligations | Quelle transformation réelle autorise le regroupement ? |
| Continuation | Quel état, quel support et quelles admissions sont prolongés ? |

Classer chaque correspondance : définition commune ; construction dérivée ;
transport exact avec deux lois de retour ; projection avec accords limités ;
absence de raccord. Une projection de présentation n'est pas une équivalence
de toute la constitution circulaire.

Ne pas transplanter automatiquement les alias ou les vues spécialisés de
l'autre projet. Identifier d'abord les abstractions nécessaires puis les
construire sur les interfaces locales. Le résultat local ne doit dépendre ni
d'un checkout extérieur ni d'une référence d'audit.

### Gate G1

Chaque famille utilisée par l'instance maître est rattachée à une primitive
locale ou à une construction dérivée documentée. Aucun carrier brut réintroduit
une ontologie indépendante en amont des rôles. Les accords non établis restent
explicitement ouverts dans le registre, jamais annoncés comme unification réussie.

Une modification des quatre fichiers protégés n'est pas autorisée par ce plan.
Si une extraction devient indispensable, expliquer sa nécessité et présenter
son périmètre de conservation avant de demander une autorisation séparée.

### Examen précoce de faisabilité de la mémoire

Avant une refonte étendue, inventorier ce que la prochaine tête lit réellement.
Dans la base, `runThreadedNextDiscovery` consomme la génération, la graine et
la provenance ; la continuation s'appuie aussi sur l'affectation et les décisions.
Identifier donc les observations futures indispensables et les données
historiques candidates à l'oubli, avec leur producteur et leurs consommateurs.

Fixer dès cet examen le domaine envisagé : toutes les réalisations admissibles
de la famille choisie, et non quelques états fabriqués pour le séparateur.
Examiner si deux préfixes réellement produits peuvent partager les observations
nécessaires tout en différant historiquement. Ne pas supposer que le séparateur
numérique du matériau comparé existe dans la famille publique.

Cet examen ne remplace pas G6 ni G7 et n'annonce pas leur réussite. Il doit
identifier avant la généralisation G5 toute incompatibilité déjà démontrable.
Si seule une extension de famille semble permettre l'oubli, soumettre cette
extension explicitement avant de la coder. L'autorisation de restreindre les
lectures futures ne vaut pas autorisation de changer la famille ou son calcul.

## 8. Lot 2 — Prototype décisif sur une tête réelle de l'exécution

Ce prototype précède la migration massive des modules de ressources.

### Construction à réaliser

1. Prendre une tête effectivement produite par le moteur public, son préfixe
   déjà construit et son contexte de découverte ; ne pas fournir une relation
   indépendante ou un état canonique substitué.
2. Constituer les ressources lues par cette tête, avec leurs occurrences,
   sortes, producteurs et références. Cela concerne notamment la matière de
   génération, la graine, la racine de recherche, les candidats, l'action
   validée et les continuations qu'elle transforme.
   Partir de l'endpoint effectivement produit par l'initialisation, puis du
   premier contexte construit depuis cet endpoint : aucune racine initiale
   reconstruite séparément ne sert de substitut.
3. Exécuter le consommateur depuis ces références. Prouver que ses données et
   sa décision sont celles de la tête auditée.
4. Construire la décomposition avant le tail, puis prolonger le support avec
   les données et témoins effectivement produits.
5. Prouver que le prochain consommateur utilise ces données produites.

Définir ici les ressources dépendantes nécessaires à la vraie tête : formule,
affectation à sa profondeur, continuation de cette formule et action entre
les continuations des deux branches exactes. Une sorte grossière `Nat`/`Bool`
ne peut pas porter ces contraintes. Toute lecture doit conserver les indices
de contexte et de branche, ainsi que l'occurrence productrice ; une égalité de
valeurs ne les remplace pas.

La tête enrichie effectue la découverte et l'application une seule fois et
en projette les données, rôles et ressources. Elle n'appelle pas deux moteurs
pour ensuite comparer leurs sorties. L'ancienne fonction sert de spécification
d'effacement, non de second calcul exécuté dans le nouveau moteur.

### Accords exigés et gate G2

- Effacement du prototype enrichi = tête publique existante.
- Action sélectionnée = action validée par cette découverte.
- Transformation des continuations et préservation = licences retournées.
- Prochain état = sortie de cette action, avec les références transportées.
- Même tête/préfixe, futurs différents : même production de tête entière.

Ces accords sont quantifiés sur le domaine explicite des états, préfixes et
témoins de fraîcheur admissibles. Un unique exemple à profondeur fixée ne ferme
pas la gate. Le certificat porte l'accord sur l'objet de production entier,
pas uniquement sur sa projection de décomposition ; c'est le renforcement
demandé par l'audit de la base.

La coïncidence de valeurs numériques ne suffit pour aucun de ces accords.
Un simple couple contenant la tête ancienne et un feedback numérique indépendant
échoue à G2. Si ce raccord ne se ferme pas, arrêter la généralisation et décrire
précisément l'obligation manquante ; ne pas reconstruire un exemple plus facile.

## 9. Lot 3 — Regroupement certifié local

### Noyau générique

Reconstituer localement les règles de pas admis, la localisation positive des
choix, la décroissance et les jonctions locales. Produire le normaliseur par
récursion structurelle et dériver terminalité, unicité, confluence et fibres.

Ne pas recevoir en entrée une cible globale, une partition finale ou une largeur
prescrite. Les jonctions sont des témoins construits dans `Type` ; une proposition
de leur existence ne remplace pas leur production.

### Raccord aux rôles existants

- Le domaine reste `RoleOccurrenceProfile roles`.
- Construire le codage éventuellement nécessaire après constitution, avec ses
  deux lois de retour, puis réindexer règles, cibles et témoins complets.
- Construire les autorisations depuis `RoleStatus.History` ; fermer le cas
  exécuté par les licences réellement retournées.
- Dériver l'accord du normaliseur avec la sélection existante ; ne pas choisir
  cette sélection comme normaliseur constant.
- Construire l'image exacte et son transport vers les obligations existantes.
- Séparer la frontière exhaustive, qui énumère les sources, de la frontière
  produite par fragments. Ne pas attribuer à la première une absence d'énumération.

Réemployer `FiniteCarrier` et les outils locaux d'image exacte lorsqu'ils
conviennent, au lieu de définir un second régime fini concurrent. Leur
`DecidableEq` doit être un algorithme effectivement fourni sur le carrier
concerné. Les cibles pouvant contenir des continuations fonctionnelles, ne pas
supposer une décision générique de leur égalité extensionnelle. Fermer une
décision sur l'image représentée, avec des codes et des lois exactes construits,
ou déclarer cette obligation ouverte ; une étiquette qui ne compare pas les
vraies fibres n'y répond pas. L'existence de l'image comme interface ne prouve
pas qu'elle est calculable dans toutes les instances.

Distinguer la cible normale de positions constituées et la sortie de l'action
sur leurs continuations. Le raccord entre l'image générique et le régime public
doit fermer leurs fibres dans les deux directions sur le domaine annoncé,
avant toute annonce de transport exact. La conservation du même nombre de
cibles ne suffit pas. Un transport réversible entre les images finies de données
canoniques n'autorise pas à inverser l'action sur les continuations arbitraires.

Le normaliseur générique peut analyser une histoire de statuts déjà achevée.
Cette analyse aval ne constitue pas la production opérationnelle de tête :
celle-ci reste construite dans l'exécution, depuis son seul préfixe. Ne pas
faire dépendre la découverte ou la décision de tête du résultat de cette analyse.

### Gate G3

Les fibres de `carry`, les fibres des cibles et les chaînes admises coïncident
dans les deux directions. Les largeurs complète `2^n`, partielle `2^k` et
exécutée un sont conservées sur leur carrier propre. Deux profils réellement
distincts sont portés ensemble sans devenir égaux.

Préciser les relations employées : une trace d'action reste dirigée ; la
codétermination signifie que deux sources ont un aboutissement normal commun.
Une chaîne symétrisée peut caractériser cette codétermination, mais son pas
inverse formel n'est pas un inverse calculable du transport d'acceptation.
Ne pas confondre égalité des cibles normales et existence d'une trace dirigée
de n'importe quel profil vers n'importe quel autre profil de sa fibre.

Le théorème de classe s'applique directement au carrier exécuté. Les preuves
générales restent conditionnelles à leurs règles locales ; le cas public ferme
ces règles par une construction réelle issue de la découverte.

## 10. Lot 4 — Actions, préservation et extensions

### Actions sur les données

Construire les actions locales à partir des transports autorisés. Composer ces
actions le long des traces et prouver la préservation pour toute donnée acceptée.
Conserver un séparateur montrant qu'une cible commune ne suffit pas à établir
l'égalité des actions sur les données.

Pour l'instance maître, fermer positivement :

- toute trace normalisante réalise la transformation autoritaire du profil ;
- depuis un même profil source et une même donnée, deux telles traces
  produisent les mêmes données transportées ;
- sur les données canoniques, cette sortie est la cible réellement exécutée.

L'égalité n'est pas limitée à une étiquette de largeur ou à un profil booléen.
En revanche, il n'est pas demandé que toutes les continuations arbitraires,
ou deux données sources différentes, convergent vers la même valeur. Dans la
base, `RoleSemantics.actProfile` agit sur les données arbitraires,
`profilePreserves` en conserve l'acceptation, et `canonicalAction_exact`
établit la convergence des seules données canoniques exécutées. Ces trois
portées doivent rester séparées dans les nouveaux types et théorèmes.
`ProfileAccept` est une acceptation locale point par point, non un résultat
nouveau de correction ou de complétude pour SAT arbitraire.

### Extensions historiques

Construire les inclusions des occurrences et ressources anciennes, le transport
des pas anciens, les références nouvelles et les licences ajoutées. Prouver
l'injectivité des identités sources conservées et la composition des transports.

Après ajout d'opérations, renormaliser dans le contexte nouveau :
`normalNew (embed (normalOld x)) = normalNew (embed x)`.
Ne pas supposer qu'un ancien terminal reste terminal sans nouvelle preuve.

### Gate G4

L'action, la préservation et la cohérence de traces issues d'une même source
sur une même donnée sont fermées sur les continuations arbitraires de
l'instance maître. La convergence vers la sortie effectivement exécutée est
fermée sur ses données canoniques, sans extension tacite à toutes les données.
Une licence historique concrète provient du producteur exécuté. Un suffixe
hypothétique fourni est distingué de la continuation réellement construite
par le moteur.

## 11. Lot 5 — Support de ressources de l'instance maître

Généraliser le prototype G2 aux histoires complètes par la même récursion.
Le support contient les producteurs typés, leurs références antérieures et
leurs accords d'évaluation ; il ne sert pas de réserve globale de réponses.

Une seule récursion construit simultanément la suite, les ressources et la
production opérationnelle, en appelant G2 avant le tail. Le nouvel état enrichi
n'a pas à être définitionnellement l'ancien état : leur raccord est l'effacement
prouvé à chaque pas. En revanche, le carrier de profils utilisé par le théorème
de classe et par le régime public doit toujours être littéralement le même,
défini une seule fois depuis les rôles de cette récursion. Ne pas déplacer cette
exigence vers une simple égalité propositionnelle entre deux carriers.

### Obligations

- Les références sont indexées par sorte et par support constitué. Une
  continuation relative à une formule ne peut être lue comme celle d'une autre.
- Une ressource produite conserve son occurrence, son ordre de dépendance et
  ses relations de formation, même lorsque sa valeur coïncide avec une autre.
- L'ordre des arguments et leurs sortes sont contrôlés séparément de l'égalité
  de valeurs ; une permutation ne devient pas légitime par égalité de lectures.
- La lecture d'une ressource doit alimenter effectivement l'opération suivante.
- L'effacement vers l'exécution existante est prouvé pour tout préfixe, pas
  seulement pour la sortie finale.
- L'effacement commute avec l'extension, l'action, les événements nécessaires
  et les transports de références.

### Gate G5

Il existe une exécution maître fermée dont les projections réalisent la chaîne
publique auditée et dont le support de ressources est celui utilisé pour cette
chaîne. Les propriétés de ressources annoncées concernent cette exécution,
pas une seconde instance numérique exécutée en parallèle.

Une classe maître plus générale peut accueillir plusieurs réalisations, mais
leurs propriétés ne sont jamais attribuées automatiquement à la réalisation
publique. Tout élargissement de sa classe d'entrées ou d'histoires doit être
énoncé et conserver la réalisation auditée comme membre explicitement raccordé.

## 12. Lot 6 — Contrat futur et mémoire réduite

### Définir le contrat avant la réduction

Fixer les entrées futures autorisées, les opérations, les lectures, les événements
et l'admission. Le contrat doit inclure ce que les prochains consommateurs de
la vraie recherche lisent, notamment les données de provenance nécessaires.
Il ne peut être réduit après observation d'un échec pour obtenir artificiellement
une mémoire plus petite.

Le contrat futur peut exclure explicitement certaines lectures rétrospectives.
Mais il ne doit pas exclure une lecture utilisée par le moteur, ni rendre
toutes les continuations impossibles. Une entrée `Unit` déterministe ne se
substitue pas à la classe des entrées réelles de l'instance maître.

Définir le domaine des états atteignables et des suffixes admissibles, y compris
leurs indices de profondeur, de formule et de support. Un regroupement de ces
états dans un type commun peut porter ces indices ; il ne doit pas les effacer.
Fermer aussi la conservation de ce domaine après chaque pas. Les lois ne
quantifient pas tacitement sur des états impossibles, et ne s'arrêtent pas à
un unique suffixe canonique si le contrat annonce toutes les reprises admises.

### Réduction à construire

Construire une projection de l'état maître vers une mémoire fermée, un pas
réduit exécutable et les transports d'admission nécessaires. Fermer les lois
locales suivantes sur des données effectivement atteintes :

| Loi | Accord exigé |
|---|---|
| Successeur | Projeter après le pas source = exécuter le pas réduit après projection. |
| Événement | Les événements contractuels produits sont les mêmes. |
| Lecture | Les lectures contractuelles de l'état correspondent. |
| Admission | Les témoins des entrées/suffixes autorisés sont transportables selon le contrat. |
| Références | Les références futures requises gardent identité, sorte et accords de lecture. |
| Reprise | La composition de deux suffixes conserve ces accords. |

Propager ces lois à toute continuation finie autorisée. Distinguer cette fermeture
d'une affirmation de terminaison ou de borne de mémoire générale.

### Gate G6

Le moteur réduit consomme uniquement la mémoire et les entrées contractuelles.
Inspecter corps des fonctions, valeurs stockées et captures des fermetures :
aucune histoire ancienne, seed cachée ou archive extérieure ne doit permettre
de contourner le contrat annoncé. Une séparation syntaxique d'import ne suffit pas.

Un témoin historique peut rester dans le support scientifique de correspondance,
mais ne doit pas être une entrée runtime dissimulée du moteur réduit.
Le contrat n'est pas présenté comme bijection avec l'histoire complète.

Le résultat runtime du moteur réduit n'embarque pas le certificat maître avec
son archive complète dans un champ de données ou une fermeture. La construction
historique de référence et la preuve de correspondance sont séparées de la
fonction de reprise et de sa mémoire effective. Les indices effacés par le
compilateur ne doivent pas dissimuler un champ calculatoire conservant l'histoire.

Séparer les interfaces publiées : l'exécution historique conserve ses théorèmes
et ses lectures complètes ; l'exécution réduite garantit uniquement les lectures
du contrat annoncé. Ce n'est pas une suppression des anciens résultats, mais
une restriction explicite de l'interface du moteur réduit. Si celui-ci conserve
en fait la lecture de toute l'histoire, un oubli irréversible est incompatible
avec ce contrat. La distinction des identités sources ne signifie pas que leur
archive complète doit rester accessible depuis la mémoire réduite.

Les lois d'admission doivent être constructives dans les deux directions sur
le domaine atteint, et suffisantes pour toute reprise autorisée. Une implication
dans un seul sens ne justifie pas une continuation dite exacte. Les indices
dépendants des entrées, références et résultats sont transportés explicitement,
pas oubliés pour obtenir un contrat artificiellement indépendant de l'état.

## 13. Lot 7 — Véritable oubli, ou impossibilité explicitée

Une mémoire réduite n'est pas automatiquement une mémoire irréversible.
Sur une famille canonique déterminée par la profondeur, conserver cette
profondeur peut suffire à reconstruire toute l'histoire.

### Preuve recherchée

Construire deux parcours admissibles de normalisation de profils réellement
constitués de l'instance maître, avec la même mémoire réduite et des profils
sources distincts. En déduire l'impossibilité d'un décodeur uniforme du profil
depuis la mémoire sur ce domaine. Fermer en parallèle la conservation de toutes
les continuations du contrat G6 depuis ces deux résultats exécutés.

La donnée perdue doit avoir participé à sa constitution ou à une action réelle,
pas être un marqueur arbitraire ajouté uniquement pour fabriquer le séparateur.
Les deux parcours ne sont pas des états contrefactuels libres sans exécution.

Fixer un même espace de mémoire et une même observation historique pour cette
comparaison. Si les parcours ont des indices dépendants différents, construire
leur domaine commun et les transports nécessaires avant d'affirmer que leurs
mémoires sont égales. La séparation recherchée a la forme suivante :

```text
project (produce profileA) = project (produce profileB)
profileA != profileB
donc aucun decode vérifiant decode (project p) = historicalRead p
pour tout résultat exécuté p du domaine fixé.
```

Le moteur réduit sait continuer depuis leur mémoire commune sans recevoir
le profil source caché. Les preuves de correspondance peuvent mentionner ces
parcours ; les fonctions de reprise ne les reçoivent pas.

### Gate G7 et limites possibles

Précision de domaine après relecture : le séparateur réalisé porte sur les
parcours de normalisation des profils déjà constitués de l'instance maître.
L'ancien domaine `PublicPrefix` n'incluait pas ces entrées. Son obstruction
reste vraie sous son contrat brut, mais ne remplace pas ce nouveau résultat.
Ne jamais présenter le séparateur comme deux préfixes chronologiques distincts
de la recherche canonique : cette affirmation n'est pas démontrée.

Si le domaine canonique actuel ne permet pas un tel couple, le dire et démontrer
la reconstruction disponible lorsque c'est possible. Ne pas transplanter le
séparateur de l'autre instance comme si le moteur public l'avait produit.

Si une extension admissible de la famille est nécessaire, la présenter avant
implémentation et conserver le membre public initial. Ne pas changer silencieusement
la cible, le contrat futur ou l'instance pour annoncer un oubli réussi.

Si une donnée dite oubliée est indispensable à une continuation autorisée,
soit une représentation suffisante est construite avec preuve, soit cette
réduction est impossible sous ce contrat. Ne pas appeler « oubli irréversible »
une simple suppression de cache suivie d'une reconstruction.

La cible ancienne demeure une obligation indépendante : l'échec de G7 ne la
rend pas fausse. En revanche, le chantier d'unification avec oubli n'est pas
déclaré terminé tant que cette obligation nouvelle n'est pas fermée ou qu'une
modification de portée n'est pas explicitement approuvée.

## 14. Lot 8 — Certificat public unifié et consommateurs

Construire un certificat dont les indices épinglent la même exécution maître,
son histoire de rôles, sa normalisation, son régime et le contrat futur réalisé.
Les accords nécessaires figurent dans ses types et ses constructions ; ils
ne sont pas remplacés par la confidentialité d'un constructeur.

Le certificat doit fermer :

- l'exactitude de toute la production de tête et son indépendance de l'horizon ;
- l'effacement de chaque préfixe vers la réalisation publique auditée ;
- les raccords d'action et de préservation sur les continuations ;
- les fibres exactes du régime et la distinction des profils sources ;
- les lectures complète `2^n`, partielle `2^k` et exécutée un sur leurs carriers ;
- la cohérence de toutes les traces normalisantes de l'instance ;
- les transports historiques et leur composition ;
- la continuation réduite et les garanties exactes du contrat futur ;
- le séparateur d'oubli effectivement établi, si G7 est fermé.

Les consommateurs scientifiques utilisent ces productions et accords, dans
l'ordre constitutif. Un champ stocké puis jamais lu ne prouve pas une nécessité.
Les théorèmes génériques sur les familles ne sont pas confondus avec les
certificats de cette réalisation concrète.

L'obligation de G7 reste distincte dans le certificat : tant qu'elle est ouverte,
ne pas produire une façade qui annonce toutes les propriétés closes. La fermeture
de G8 est celle de l'unification complète demandée, pas seulement du phénomène
ancien auquel on aurait ajouté des champs optionnels.

### Gate G8

Un client important uniquement `RelationalPerimeter` accède aux déclarations
scientifiques closes et peut appliquer directement le `iff` au régime public.
Il ne reçoit pas un singleton indépendant ni une instance native étrangère
comme remplacement de l'image réellement exécutée.

## 15. Lot 9 — Validation constructive et contrôle de conservation

### Sources et calculabilité

- Aucun `axiom`, trou, `sorry`, `noncomputable`, `Classical`, `propext` ou
  `Quot.sound` introduit dans les déclarations écrites.
- Toute construction de données constitutives est exécutable ; aucune preuve
  propositionnelle ne sert à cacher un producteur non calculable.
- Les lois sur les actions sont prouvées point par point sur leurs données.
  Ne pas les convertir par une extensionalité fonctionnelle dépendant de
  `Quot.sound`. Une égalité de fonctions n'est utilisée que si sa preuve reste
  dans les dépendances constructives autorisées.
- Un seul bloc final `AXIOM_AUDIT` par fichier, noms complets existants et
  dépendances axiomatiques vérifiées. Étendre le contrôle à tous les fichiers
  du périmètre, et non à une liste privilégiée de modules.
- Distinguer dans le sweep les déclarations écrites des lemmes générés par Lean.
  Aucun lemme manuscrit ne consomme une dépendance interdite.

Le défaut des 86 fichiers de l'autre arbre n'est pas recopié : chaque module
reconstruit satisfait la règle locale dès sa première livraison.

### Contrôles proportionnés aux obligations

Les preuves sont la validation principale. Des probes de clients et des
modifications isolées contrôlent en complément les frontières précises :

| Frontière | Contrôle attendu |
|---|---|
| Source constituée | Un produit binaire nu ne remplace pas directement le carrier scientifique. |
| Production de tête | Une reconstruction depuis un futur terminé ne ferme pas le même certificat. |
| Action | Une action indépendante de la découverte ne remplace pas l'action exécutée. |
| Préservation | Sa suppression empêche la construction qui l'exige, pas seulement un test de nom. |
| Image du régime | Un `Unit` indépendant ne remplace pas l'image produite. |
| Données transportées | Une cible commune n'autorise pas deux actions différentes sans loi de cohérence. |
| Ressources | Mauvaise sorte, mauvaise occurrence ou arguments permutés sont rejetés. |
| Continuation | Tail étranger ou reprise utilisant une archive cachée ne ferme pas le contrat. |
| Oubli | Un décodeur de la donnée perdue contredit le couple positif construit. |

Un échec de compilation ne vaut preuve de frontière que si sa raison attendue
est constatée ; un timeout, un import manquant ou une erreur sans rapport ne
constitue pas une validation. Les contrôles restent dans des copies isolées.
Ils ne remplacent pas la démonstration ni ne redéfinissent la cible.

Une obligation peut être reconstruite positivement depuis les mêmes données
constitutives : cela n'est ni une perte ni une triche. Par exemple, supprimer
un champ de distinction puis reprouver cette distinction depuis les positions
constituées n'efface pas la séparation. Contrôler la dépendance scientifique,
pas la nécessité syntaxique du nom d'un champ. De même, après convergence,
un `carry` constant peut satisfaire les seules égalités de fibres ; ces égalités
ne suffisent donc pas à elles seules à établir la provenance exécutée du régime.
Les indices, producteurs et raccords exacts du certificat restent nécessaires.

### Gate G9

Les builds propres, vérificateurs Windows/Bash disponibles, probes, audits,
imports, liens et tests passent. Le registre G0 identifie pour chaque ancien
résultat sa conservation, son raccord ou une difficulté encore ouverte.
Aucune perte de résultat n'est masquée par la suppression de son consommateur.

## 16. Lot 10 — Documentation, audit indépendant et publication

### Documentation permanente

Mettre à jour les versions française et anglaise, le README et les instructions
de reproduction après fermeture des gates correspondantes. Distinguer clairement :

- ce qui est donné, constitué, découvert et démontré ;
- les garanties générales conditionnelles et leur réalisation concrète ;
- la largeur complète, la largeur partielle et le coût du calcul ;
- la mémoire réduite, la conservation future et la perte historique prouvée.

Ne pas écrire que les propriétés d'une autre instance appartiennent à la maître.
Ne pas remplacer la cible citée par un résumé documentaire plus facile.
Un éventuel nouveau schéma est un livrable séparé ; aucun SVG existant n'est
modifié par défaut.

### Audit indépendant

Après vérification interne, préparer un prompt anglais avec dépôt, branche,
SHA distant complet et base exacte, sans placeholder. L'audit examine la cible
ancienne inchangée et les obligations nouvelles d'unification séparément.
Il doit suivre les producteurs et consommateurs, les témoins communs, les
transports, le contrat futur et l'absence d'une seconde instance substituée.

L'envoi externe, le commit, le push, l'ouverture de PR et la fusion nécessitent
leurs demandes explicites. Un verdict externe ne devient pas une preuve Lean.
Toute incompatibilité de toolchain du service est déclarée avant soumission.

### Gate G10

Le paquet audité contient exactement les sources, dépendances locales et
documents du commit annoncé. Aucun cache ou checkout extérieur n'est requis.
Les résultats sont reliés aux commandes et empreintes de ce paquet. Toute
correction entraîne une nouvelle version du protocole et de l'évidence.

Avant PR vers `main`, retirer les documents de chantier, copies brutes et
références inutiles ; régénérer le manifeste depuis l'arbre final ; vérifier
les liens, la licence, le diff et les builds. Après fusion explicitement
autorisée, refaire les contrôles sur le commit fusionné. Une PR ouverte ne
signifie pas que le chantier est terminé.

## 17. Ordre d'exécution et décisions de blocage

```text
G0 référence reproductible
  -> G1 correspondances de fondation et faisabilité préliminaire de la mémoire
  -> G2 tête réelle, ressources réellement consommées
  -> G3 regroupement natif exact
  -> G4 cohérence des actions et extensions
  -> G5 instance maître à support commun
  -> G6 contrat futur fermé et moteur réduit
  -> G7 oubli réel sur cette instance
  -> G8 certificat public unifié
  -> G9 conservation et validation locale
  -> G10 audit exact puis publication autorisée
```

Les lots peuvent partager des lectures et preuves auxiliaires ; leurs conclusions
ne sont pas déclarées closes avant leur gate. L'obligation la plus risquée est
G7 : l'existence d'un véritable oubli sur la même instance et sous un contrat
non vide n'est pas garantie par le présent plan.

Si une gate échoue, fournir la déclaration précise, les hypothèses, la raison
et l'effet sur les objectifs. Ne pas remplacer la réalisation demandée par
un jouet, une hypothèse externe ou un résultat de cardinalité.

## 18. Relecture du plan avant implémentation

La seconde passe a contrôlé le plan contre `lakefile.toml`, la récursion de
`CausalOperationalExecution`, les portées de `RoleProfileSemantics` et les
interfaces de ressources et de continuation du matériau comparé. Elle a corrigé :

- l'ambiguïté entre préservation arbitraire et convergence canonique ;
- l'absence d'un raccord explicite de l'initialisation et d'une seule récursion ;
- le manque d'exigences précoces sur les ressources à indices dépendants ;
- la confusion possible entre analyse d'une histoire achevée et production de tête ;
- l'intégration incomplètement spécifiée des nouveaux chemins dans Lake ;
- le périmètre des lectures conservées et la comparaison typée des préfixes oubliés ;
- la distinction entre trace dirigée et chaîne symétrisée de codétermination ;
- une lecture trop syntaxique de la nécessité des témoins.

La troisième passe a confronté le plan aux lectures de `ThreadedConstitutiveState`,
à `runThreadedNextDiscovery`, à la portée de `RoleStatus.History` et au contrat
de l'oubli natif comparé. Elle ajoute deux exigences : distinguer les politiques
mixtes de l'exécution publique, et examiner la faisabilité de l'oubli avant la
refonte étendue. Elle distingue également le lemme cardinal général de la
consommation relationnelle requise dans la réalisation concrète.
Elle explicite aussi les décisions d'égalité nécessaires aux images finies,
le réemploi des régimes locaux et l'absence d'archive dans le résultat runtime
réduit : ce sont des obligations de construction, pas des propriétés acquises.

Les invariants suivants restent imposés :

- Le chantier appartient à `relational-perimeter`, pas au dépôt servant de matériau.
- Sa base est le commit indépendant validé, et non un worktree plus récent.
- Les quatre fichiers initiaux restent protégés ; les modules ajoutés en dérivent.
- La cible est citée intégralement et son `iff` conserve sa portée exacte.
- Le résultat partiel ancien n'est pas réattribué au nouvel apport.
- Le regroupement générique doit être fermé sur les occurrences et actions des rôles.
- La continuation native étrangère n'est pas annoncée comme celle du moteur public.
- Le prototype de tête ferme le raccord concret avant généralisation.
- L'oubli exige deux réalisations admissibles et un contrat futur fixé au préalable.
- Le plan explicite le cas où cette obligation est impossible sur le domaine actuel.
- Aucune nouvelle borne de coût, nouveauté informationnelle ou résolution de SAT
  n'est promise par une largeur un.
- La publication finale est autonome et ne conserve pas ce document temporaire.

Ces contrôles valident la structure du plan, pas la réussite anticipée de son
implémentation. Au moment de sa création, aucun lot de code n'avait été commencé.
L'état effectif est désormais consigné en tête du document ; les obligations
non fermées y restent explicitement nommées.
