# Rapport de vérification de l’alignement constitutif neuronal

## Révision examinée

- Projet : `JohnDoe-collab-stack/relational-perimeter`
- Branche : `codex/constitutive-neural-alignment-implementation`
- Commit : `fafd739b7f4718ab9939ccd870eb4983a4655d2e`
- Parent : `6a767f934556e2babdd4a43121a293364227db3c`
- Arbre Git : `71d471501f31f62c937c3f1650d099f40cd1e9cb`
- Révision distante : identique à la révision locale examinée
- État de l’arbre avant vérification : propre
- Nature de l’examen : vérification interne conceptuelle, technique et
  scientifique de la cible complète

Ce rapport vise exclusivement la révision indiquée. Il ne constitue pas un
audit indépendant et ne doit pas être utilisé comme substitut aux deux audits
externes exigés par la cible terminale.

Complément documentaire du 22 octobre 2026 : les exigences et les critères de
comparaison ci-dessous ont été confrontés à la
[cible terminale](CIBLE_ALIGNEMENT_CONSTITUTIF_INCREMENTAL.fr.md) et aux
[critères C1–C18](CONSTITUTIVE_NEURAL_ALIGNMENT_TARGETS.fr.md). Ces deux
documents restent les références obligatoires intégrales. Le présent rapport
précise leur mise en œuvre et leurs preuves de clôture, sans les remplacer par
sa liste abrégée de corrections. Les résultats de commandes rapportés restent
ceux de l’examen de `fafd739` ; ce complément ne constitue pas une nouvelle
campagne de compilation ou de mesure.

L’étude bibliographique intégrée le même jour porte sur le gain scientifique
visé en cas de réalisation complète. Les références R1–R8, les épreuves P1–P8
et les critères S1–S8 ci-dessous deviennent obligatoires pour la comparaison.
Ils ne changent ni les verdicts historiques sur `fafd739`, ni les garanties
G1–G10, ni les exigences C1–C18. Ils ne certifient pas les modifications en
cours dans l’arbre de travail.

Un complément de spécification du 22 octobre 2026 explicite désormais le
raccord constitutif RC1–RC6 dans le plan et dans ce rapport. Il est obligatoire
en plus des garanties et comparaisons existantes. Il ne constitue ni un nouvel
audit de `fafd739`, ni une validation des corrections locales en cours. Les
constats historiques, les dix défauts et les résultats de commandes de la
révision examinée sont conservés.

## Verdict binaire

**La cible terminale d’alignement constitutif neuronal n’est pas atteinte à
cette révision.**

Le noyau formel a néanmoins fortement progressé. Le méta-contrat exécutable,
le vérificateur initial générique, l’analyse incrémentale générique, le runtime
fermé, la trace dépendante, l’adaptateur de l’artefact appris et la séparation
entre `alignedUpdate` et `bypassUpdate` sont réellement présents. Le dépôt
compile, les audits d’axiomes réussissent et aucune régression Lean n’a été
détectée dans les contrôles exécutés.

Ce verdict négatif ne provient donc pas d’une disparition du socle déjà
construit. Il provient d’obligations terminales encore ouvertes et de plusieurs
raccords internes qui ne réalisent pas encore la chaîne constitutive unique
exigée par la cible.

## Résultats effectivement établis

### 1. Méta-contrat exécutable

`ExecutableMetaContractInterface` fournit une interface paramétrique de
décodage et de décision. Le vérificateur initial `checkInitial` est défini à
partir de cette interface et n’est plus limité, dans sa signature générique, à
la seule instance publique.

Le progrès est substantiel : le dépôt possède désormais un lieu formel où les
décisions de contrat, le décodage et leurs lois de réflexion peuvent être
rassemblés sans introduire un `CheckedAgent` préfabriqué dans l’entrée.

### 2. Certificat d’état fragmenté et assemblé

`StateCertificateFragments` décompose les obligations constitutives et
`assembleStateConstitution` reconstruit le certificat cible depuis les
fragments fournis. La cible n’est plus simplement rangée à côté d’un certificat
complet construit indépendamment.

### 3. Production commune des transitions

`TransitionProductionKernel` et `produceTransition` fournissent un noyau
commun à la production de transition. Cette factorisation rapproche le recheck
de référence et le chemin incrémental d’une même sémantique de transition.

### 4. Vérificateur incrémental générique

Le dépôt contient notamment :

- `IncrementalTargetAnalysis`
- `IncrementalCheckerEngine`
- `buildIncrementalCheckedUpdate`
- `checkGenericIncrementalUpdate`

Le checker produit un `CheckedUpdate` dépendant à partir d’une analyse et de
fragments assemblés. Le résultat n’est plus seulement une observation externe
sur deux artefacts déjà certifiés.

### 5. Trace finie dépendante et runtime fermé

`CheckedReconfigurationTrace`, `CheckedUpdateProgram` et `checkUpdates`
construisent une trace dépendante. `CertifiedRuntime` possède un constructeur
privé et `submitUpdate` est l’opération générique publique qui tente
l’installation d’une mise à jour.

Le runtime conserve son historique, son état certifié et les obligations
associées au contrat courant.

### 6. Raccord de l’artefact appris à l’API générique

L’artefact appris passe maintenant par :

- `learnedExecutableMetaContractInterface`
- `checkInitial`
- le checker incrémental générique
- `CertifiedRuntime`
- `submitUpdate`

Les deux candidats partent du même agent initial certifié. La mise à jour
alignée est acceptée et le contournement est rejeté par la même API fermée.
Le chemin rejeté ne produit pas de runtime successeur installable.

### 7. Divergence future opérationnelle

`LearnedOperationalFutureDivergenceCertificate` rassemble :

- l’équivalence sur une table courante annoncée
- la factorisation des vérificateurs extensionnels
- un futur non vide
- le futur aligné lu depuis l’état installé
- la violation contrefactuelle du contournement
- l’acceptation et le rejet par le runtime
- l’absence de successeur installé pour le contournement

Cette partie constitue une amélioration réelle par rapport au simple test
d’égalité des sorties courantes.

### 8. Renforcement des frontières négatives

Les fixtures négatives couvrent les principaux contournements introduits par
la généralisation. Elles protègent notamment la construction privée du runtime,
la production du successeur, l’assemblage des fragments et l’impossibilité
d’installer directement une mise à jour rejetée.

## Défauts conceptuels et techniques bloquants

### 1. Le domaine courant de l’instance apprise n’est pas unique

Le contrat opérationnel exécuté par le runtime utilise
`independentLearnedDeclaredInputs`, qui contient une seule entrée. Cette même
liste est employée par les bases apprises raccordées au runtime.

La preuve d’équivalence comportementale et le protocole comparatif v4 utilisent
séparément `learnedRuntimeDeclaredCurrentDomain`, qui contient quatre entrées.
Le protocole qualifie cette liste de domaine courant déclaré et lui attribue la
cardinalité quatre.

Il existe donc deux objets différents présentés comme le domaine courant de la
même expérience :

1. le domaine réellement stocké dans le `ConstitutiveContract` exécuté
2. le domaine employé par le théorème d’équivalence et le protocole

La chaîne actuelle n’établit pas que l’équivalence porte sur le domaine courant
déclaré du contrat réellement exécuté.

#### Correction obligatoire

Définir une seule liste canonique de domaine courant, puis la faire consommer
par :

- le contrat opérationnel
- l’agent initial
- les deux mises à jour candidates
- le vérificateur extensionnel
- le certificat de divergence future
- le protocole comparatif

Une alternative acceptable serait de dériver formellement chaque vue depuis
une même source et de prouver leur égalité exacte. Deux constantes parallèles
sans raccord formel ne sont pas acceptables.

### 2. `transitionDecision` est stocké mais non consommé

`ExecutableMetaContractInterface.transitionDecision` est déclaré et renseigné
par les instances publique et apprise. Aucun checker ne l’invoque dans son
chemin d’acceptation.

Le checker public compare à une transition publique attendue. L’analyseur
appris sélectionne directement l’analyse de la cible alignée. La décision du
méta-contrat n’est donc pas l’opération qui autorise effectivement la
transition installée.

Dans la méthode constitutive du dépôt, la présence d’un témoin dans une
structure ne prouve pas sa consommation exécutée.

#### Correction obligatoire

Le chemin générique doit appeler `transitionDecision` sur le contrat source,
le contrat cible et les données décodées de la même mise à jour. Le succès de
cette décision doit produire le témoin exact consommé par la production de
transition et par l’assemblage du `CheckedUpdate`.

### 3. `SerializedConstitutiveUpdate` ne nourrit pas la chaîne réelle

`SerializedConstitutiveUpdate` existe, mais il n’est consommé ni par le
checker incrémental ni par le runtime. Le chemin public utilise
`IncrementalNeuralUpdate` et le chemin appris utilise encore une représentation
candidate propre à l’instance.

La cible demandait une représentation sérialisée complète raccordant
effectivement décodage, méta-contrat, transition, vérification et soumission au
runtime. La simple présence du type et d’un test de construction ne ferme pas
cette obligation.

#### Correction obligatoire

Faire de la mise à jour sérialisée l’entrée sans preuve commune des chemins
public et appris. Son décodage doit produire les seules données admises pour :

- déterminer le contrat cible
- calculer la correspondance stable
- matérialiser l’artefact cible
- décider la transition de contrat
- calculer le cône affecté
- lancer le recheck ou le checker incrémental
- appeler `submitUpdate`

### 4. Le recheck complet de référence n’est pas générique

`checkReferenceUpdate` reconnaît encore la cible publique littérale et le
successeur public associé. Il n’existe pas de moteur générique de recheck
complet symétrique du moteur incrémental générique.

Le dépôt ne démontre donc pas encore, pour toute mise à jour sérialisée du
domaine annoncé, que le chemin incrémental et un recalcul complet indépendant
vérifient le même artefact cible et produisent le même `CheckedUpdate`.

#### Correction obligatoire

Construire un recheck complet paramétrique qui :

1. décode la mise à jour commune
2. décide la transition au moyen du méta-contrat
3. matérialise et exécute la cible
4. recalcule tous les fragments depuis cette exécution
5. assemble le certificat complet
6. retourne le `CheckedUpdate` exact

Le checker de référence ne doit pas consommer le verdict ni le certificat
final du chemin incrémental.

### 5. La complétude incrémentale générique est circulaire

`GenericIncrementalUpdateLocalConditions` affirme essentiellement qu’il existe
une analyse telle que `engine.analyze update = .ok analysis`. Le théorème de
complétude conclut ensuite que le checker réussit depuis ce même succès de
l’analyseur.

Cette formulation est logiquement valide, mais elle ne caractérise pas de
façon indépendante les conditions constitutives locales annoncées. Elle ne
permet pas de vérifier que l’analyseur est complet relativement à une famille
finie de décisions définie avant son résultat.

#### Correction obligatoire

Définir les conditions locales indépendamment du retour de `engine.analyze` :

- décodage réussi
- transition admise
- correspondance stable valide
- cône affecté exact
- transports hors cône autorisés
- recalculs dans le cône réussis
- couverture et cohérence des fragments
- exécution et successeur exacts

Puis démontrer les deux implications entre ces conditions et la réussite du
checker. L’instance apprise doit posséder la même garantie, et pas seulement
une analyse exacte codée pour le candidat aligné.

### 6. Le moteur générique peut recevoir une analyse dépendante déjà complète

`IncrementalCheckerEngine.Analysis` est arbitraire. Sa fonction `target` peut
retourner un `IncrementalTargetAnalysis` contenant déjà l’artefact, l’état,
les fragments, la transition et l’exécution cibles.

Cette interface conditionnelle est légitime, mais son existence ne démontre
pas à elle seule que le checker a calculé ces ressources depuis la mise à jour
reçue. La charge scientifique reste sur chaque analyseur concret.

#### Correction obligatoire

Pour chaque instance terminale, montrer par la structure des données et les
dépendances des preuves que l’analyse :

- provient du décodage de la mise à jour reçue
- consomme la décision effective du méta-contrat
- calcule le cône depuis les changements décodés
- transporte et recalcule réellement les fragments
- produit la transition et l’exécution depuis la même source

Les analyses littérales peuvent rester comme régressions, mais pas comme
fondement unique du claim terminal.

### 7. Le protocole de comparaison de capacité n’a pas été exécuté

Le protocole v4 fixe correctement les objets, les six classes de comparaison,
les huit capacités et le vocabulaire des verdicts. Il annonce cependant :

- `confirmatory_results_present: false`
- `confirmatory_run_permitted: false`
- six adaptateurs `required-before-confirmatory-run`
- six états d’exécution `not-run`

Ce protocole est une préparation rigoureuse. Il ne constitue pas une
comparaison de capacité réalisée.

#### Correction obligatoire

Implémenter et geler les six adaptateurs, enregistrer leurs empreintes, puis
exécuter une seule campagne confirmatoire sur les mêmes artefacts, candidats,
domaines, futurs et contrat. Une absence d’adaptateur ne doit jamais être
convertie en incapacité de la baseline.

Appliquer également les exigences de la section « Comparaison obligatoire et
preuve du gain scientifique » ci-dessous. La correction des objets communs,
notamment du domaine courant, exige une nouvelle version du protocole si elle
modifie les données ou règles figées de v4. Le protocole historique et ses
résultats éventuels restent attachés à leur propre matériel.

### 8. Le passage à l’échelle du checker certifié reste ouvert

La campagne v5 appelle bien les définitions compilées du checker Lean. Elle
mesure cependant mille répétitions du même petit artefact public fixe. Son
protocole exclut explicitement toute loi de passage à l’échelle.

Les campagnes v2 et v3 portent sur des modèles Python distincts et ne peuvent
pas servir de mesures du checker Lean certifié.

#### Correction obligatoire

Construire une famille paramétrée d’artefacts et de deltas consommée par le
même checker compilé. Pour chaque taille, les chemins incrémental et complet
doivent viser le même artefact et la même propriété. Il faut rapporter
séparément :

- largeur du profil
- taille du graphe causal
- taille du cône affecté
- fragments transportés
- fragments recalculés
- coût d’exécution
- coût de vérification
- coût physique observé

Mesurer aussi la longueur de la trace de reconfiguration, la taille du
certificat initial et du delta de certificat, et distinguer les temps de
vérification initiale, incrémentale et complète. Le graphe causal pertinent
doit croître avec la famille, au-delà de la répétition d’une instance fixe.

Une seule instance maître doit rester la source de chaque run.

Une économie pratique n’est acquise que si les mesures montrent une réduction
face au recheck complet de la même propriété sur le même artefact. Une mesure
défavorable ou sans gain doit être publiée comme telle. Elle ne permet ni de
revendiquer une accélération, ni de changer après coup la propriété comparée.

### 9. Les gates scientifiques officielles ne passent pas

`lake build` réussit, mais `verify.ps1`, le gate statique et le gate Lean
s’arrêtent sur :

```text
SCIENTIFIC_DOCS_ERROR: STALE_SOURCE: TARGET_1
```

La source suivie par `TARGET_1` a changé. Cette erreur ne démontre pas un
affaiblissement des preuves concernées, mais elle invalide leur évidence
enregistrée à la révision examinée.

#### Correction obligatoire

Identifier la dépendance exacte modifiée, rouvrir la revue du claim concerné,
relire son passage canonique et ses déclarations, puis seulement produire une
nouvelle empreinte sur une révision d’évidence gelée. Une substitution
mécanique d’empreinte est interdite.

### 10. La livraison scientifique C18 est absente

Le registre ne contient pas encore de claim terminal pour l’alignement
constitutif neuronal. Il manque :

- un identifiant de claim
- un passage canonique français
- une version anglaise relue indépendamment
- la portée et les exclusions exactes
- les déclarations Lean de production et de test
- un commit d’évidence existant
- les protocoles et résultats réellement cités
- un audit indépendant de validité
- un audit comparatif indépendant de portée et de nouveauté

Les documents présents sous `docs/work/` restent des documents de chantier.

## Garanties obligatoires à démontrer ensemble

Ces garanties explicitent la cible déjà fixée. Elles ne sont pas déclarées
acquises par leur inscription dans ce rapport. Pour chacune, la livraison doit
identifier les énoncés Lean complets, les hypothèses, les producteurs exécutés,
les transports, les consommateurs et les tests associés, sur la même révision.

| Garantie | Preuve de clôture requise | Raccord à la cible |
| --- | --- | --- |
| G1 — Évolution autorisée des contrats | Un même méta-contrat est fixé avant la trace. L’admission et chaque transition sont décidées puis consommées. Les obligations persistantes sont transportées et les obligations invalidées revérifiées avant installation. Le contrat cible ne peut pas être affaibli après examen du candidat pour le faire accepter. | Contrat constitutif, vérificateur et objectif terminal |
| G2 — Authenticité de la chaîne exécutée | Encodage, occurrences neuronales, proposition, action, effet et successeur proviennent du même run maître. Les transformations locales sont effectivement calculées et composées. L’exactitude finale est dérivée, sans être reçue dans l’entrée. | C3, C4, C11, C15, C16 |
| G3 — Dépendances causales conservées | L’exigence, le contexte et les ressources prescrites du système antérieur participent réellement à la production. Les rôles causaux requis sont établis par les interventions annoncées. L’autorisation est incorporée et consommée. Ces obligations persistent à chaque étape. Une arête présente, un poids nul ou un témoin simplement stocké ne suffisent pas. | C2, C5, C6, C7 |
| G4 — Généralité sur les traces | Le théorème porte sur toute trace finie acceptée, avec ses contrats successifs admis. Chaque queue consomme exactement le successeur produit. Une trace publique de longueur fixée ne remplace pas cette quantification. | C1, C6, trace vérifiée |
| G5 — Refus avant effectuation | Tout état accessible par l’API possède sa trace certifiée. Une mise à jour rejetée ne produit ni action effective ni successeur installé. Aucun chemin public d’effectuation ne court-circuite le certificat retourné. La simulation contrefactuelle reste pure. | Fermeture de l’API, objectif terminal |
| G6 — Oubli exécuté et futurs préservés | Deux états historiquement distincts alimentent un oubli non trivial, avec preuve de non-récupérabilité de l’origine depuis la mémoire réduite. La réalisation exacte préserve les autorisations, événements, readouts et continuations requis, pour toute liste finie de requêtes couverte par le contrat. Une liste d’exemples ne remplace pas cette quantification. | C8, C9, C10, conservation exacte des futurs |
| G7 — Vérification calculable et non circulaire | L’entrée sérialisée est sans certificat cible. Le checker construit ses preuves depuis les décisions exécutées. Correction et complétude relative portent sur un domaine et une base d’interventions finis annoncés, avec des conditions locales définies indépendamment de son succès. | Domaine décidable, vérificateur, C17 |
| G8 — Réutilisation exacte | Les identités stables et le cône couvrent réseau, décodeur, action, effet, successeur, mémoire et contrat. Les fragments hors cône sont effectivement transportés, les autres recalculés, puis assemblés. L’équivalence avec le recheck générique indépendant est démontrée sur le même résultat. | Vérification incrémentale, C16 |
| G9 — Réalisations positives substantielles | L’artefact appris indépendant satisfait les exigences de provenance et de non-trivialité. Une exécution acceptée comporte plusieurs reconfigurations successives et les constructions positives exigées par C12. Le théorème universel ne peut être satisfait seulement parce que toutes les mises à jour sont refusées ou qu’aucune trace non vide n’est possible. | C12, instance scientifique indépendante |
| G10 — Contournement latent effectivement distingué | Depuis le même agent initial certifié et la même intention admise, les candidats ont le même comportement sur tout le domaine courant canonique. La même API accepte le candidat aligné et refuse le contournement. Une continuation non vide du contrat exact montre la satisfaction alignée et la violation contrefactuelle. | Critère scientifique discriminant, expérience de séparation |

Pour G6, le domaine courant fini sert aux décisions locales annoncées. Il ne
réduit pas la garantie sur tous les futurs couverts à un échantillon de tests.
Les lois locales de simulation doivent alimenter `ExactRealization`, puis le
théorème de préservation de toute continuation finie.

Pour G9, la pluralité des reconfigurations est une preuve positive de
non-vacuité. Elle ne fixe aucune longueur maximale au théorème générique. Les
instances doivent exercer les changements et les obligations qu’elles sont
censées démontrer, sans tout réduire à des transitions identitaires.

Pour G10, le contrat et la base causale sont fixés avant le verdict. Le rejet
doit résulter de la dépendance manquante effectivement vérifiée, et non du nom
du candidat ou d’une table spéciale des réponses attendues. La continuation
future justifie la pertinence contractuelle de la distinction causale.

Le théorème sur les vérificateurs extensionnels doit conserver sa portée
exacte : un verdict qui dépend uniquement de la table courante donne le même
résultat sur les deux candidats. Ce verdict peut être un refus pour les deux.
Ce théorème ne prouve donc pas que ces vérificateurs acceptent nécessairement
le contournement, ni que toute autre méthode de vérification échoue.

## Raccord constitutif obligatoire — complément au plan

La spécification de référence est la section « Raccord constitutif obligatoire —
origine et portée des obligations » de la
[cible terminale](CIBLE_ALIGNEMENT_CONSTITUTIF_INCREMENTAL.fr.md).
Les critères RC1–RC6 y sont définis une seule fois. Le tableau suivant précise
leur contrôle dans ce rapport ; il ne remplace ni ces critères, ni G1–G10,
ni C1–C18, ni les comparaisons R1–R8, P1–P8 et S1–S8.

L'ordre à établir est : schéma contractuel reçu et fixé, production maître
exécutée, obligations instanciées sur son état et ses occurrences, certificats
issus de cette même production, contraintes démontrées, puis application à
une réalisation.
Le sens des obligations n'est pas adapté à la projection candidate ou défini
par le succès de leur propre contrôle. Les besoins normatifs reçus ne sont
pas inventés ni justifiés par l'exécution ; les conséquences certifiées de
leur instanciation ne sont pas reçues comme conclusions déjà acquises.

Le contrôle distingue le contrat opérationnel `c : ConstitutiveContract`,
les obligations `…At state` indexées par l'état exact produit, puis le contrat
d'observation `c.futureContract` et le raccord `c.futureSourceOfState state`.
Il n'exige pas un nouveau contrat complet par run ni une seconde API. Un
changement de contrat suit les transitions admises déjà requises.

RC3 interdit la circularité du contrôle, pas l'usage de ressources certifiées :
un certificat antérieur peut être consommé avec les transports requis, et une
décision exécutée peut être réfléchie en témoin d'une obligation définie
indépendamment de son succès. Produire l'état depuis l'artefact examiné et
calculer les certificats de conformité depuis cet artefact restent nécessaires.
En revanche, les témoins sources fondant la contrainte universelle sont
construits sans recevoir la projection ni supposer l'exactitude de la
réalisation candidate à laquelle elle s'appliquera.

| Critère du plan | Contrôle obligatoire et preuve de clôture | Raccord existant |
| --- | --- | --- |
| RC1 — Origine déclarée | Cartographier les paramètres reçus et les sorties calculées, avec leurs lois et leur ordre de fixation. Distinguer norme, admission et satisfaction. | G1, C15 |
| RC2 — Instanciation authentique | Lire les producteurs et consommateurs complets : les obligations `…At state` et leurs témoins concernent l'état et les mêmes occurrences du run maître, sans reconstruction indépendante. Vérifier le raccord de cet état aux sources du contrat de futurs. | G2, G3, G7 |
| RC3 — Indépendance de la réalisation | Examiner types et dépendances pour exclure une obligation source définie par la projection à valider ou par le succès de son propre contrôle. Vérifier que les producteurs des témoins sources de la contrainte universelle ne reçoivent pas la projection et ne supposent pas l'exactitude candidate, tout en permettant les certificats antérieurs et la réflexion décrits ci-dessus. | G1, G7 |
| RC4 — Conséquences générales démontrées | Exiger les énoncés pour tout type mémoire `M` et toute `ExactRealization c.futureContract M`, puis leur application aux sources neuronales produites. Réutiliser les théorèmes génériques existants. Tout séparateur revendiqué doit provenir de témoins de la même production raccordés aux observations. | G6, C10, C11 |
| RC5 — Transport effectif | Suivre les obligations jusqu'au certificat consommé par l'installation, avec les correspondances de versions, transports hors cône et recalculs des obligations invalidées. | G4, G5, G8 |
| RC6 — Possibilités positives et prévention | Fermer le raccord sur les transformations non identitaires, reconfigurations successives et oublis autorisés requis, avec une réalisation exacte témoin du même contrat, ainsi que sur le contournement refusé avant effet. | G6, G9, G10, C3, C8, C9, C12 |

La portée universelle de RC4 concerne les observations de `c.futureContract`
fixé, appliquées aux sources issues du raccord avec l'état produit. Le lemme
générique `ExactRealization.distinct_memory_of_separator` n'est pas à
redémontrer ; son application exige le séparateur neuronal et ses dépendances.
Une dépendance causale ou une autorisation n'est pas automatiquement
une observation de `FutureContract` : le raccord doit être construit lorsqu'il
est utilisé. Les garanties causales non couvertes par ce contrat gardent leurs
preuves propres. La quantification sur les réalisations exactes ne remplace ni
celle sur toutes les traces finies acceptées, ni les transports dirigés requis,
ni les preuves de refus avant effectuation.

La réalisation positive est le cas central du chantier neuronal. Gödel
illustre une frontière extrême d'incompatibilité, pas une étape imposée. Aucun
énoncé indécidable, témoin gödelien ou théorème diagonal ne doit être nécessaire
pour établir ce raccord neuronal. La conservation des résultats antérieurs
reste obligatoire, sans que leur contenu diagonal devienne une prémisse de
l'alignement neuronal.

Les corrections du domaine, du décodage, de la décision de transition et des
analyseurs doivent donc être examinées aussi sous RC1–RC5. Les fixtures doivent
atteindre les substitutions désignées dans le plan, avec les diagnostics
exacts ; une fixture existante peut être réutilisée si elle couvre réellement
la même obligation. Les instances positives déjà requises doivent fermer RC6.
Le présent complément n'affirme pas que ces obligations nouvelles d'explicitation
sont déjà fermées dans la révision auditée ou dans les changements locaux.

Les protocoles futurs devront exposer, pour chaque méthode comparée, ce qui
est prescrit en entrée, ce qui est instancié et ce qui est certifié depuis
l'exécution. Une baseline capable de recevoir le même schéma et les mêmes
témoins doit les recevoir selon l'interface déclarée. Aucune supériorité n'est
déduite du seul mot « constitutif » ou de l'absence de diagonalisation.
L'audit de validité devra contrôler RC1–RC6 et leurs consommateurs sur la
révision gelée ; l'audit de portée devra examiner ce raccord avec les autres
garanties, sans substituer ce nouveau contrôle aux comparaisons requises.

## Étude comparative du gain scientifique visé

Le raccord RC1–RC6 décrit dans la section précédente entre dans le périmètre
de la comparaison et des audits à venir, sans supprimer aucune capacité,
baseline ou épreuve déjà requise.

### Objet et statut de l’étude

La question étudiée est la suivante : la réalisation complète de la cible
apporterait-elle une capacité scientifique propre, au-delà de composants de
vérification déjà connus ? L’objet comparé est la continuité certifiée de
l’alignement constitutif pendant les transformations d’un agent appris.
L’étude ne porte ni sur le choix de valeurs humaines, ni sur une substitution
du contrat constitutif par un objectif comportemental.

Le noyau du résultat visé est le raccord, sur une même succession exécutée,
des dépendances causales prescrites, de l’action et de son effet, du successeur
produit, des transitions de contrats, de l’oubli exact et de la réutilisation
des certificats. Les relations et occurrences constitutives restent premières.
Les tableaux de sorties et les mesures de coût sont des observations aval.

L’examen préparatoire du 22 octobre 2026 a recherché les travaux sur le code
auto-modifiant certifié, la causalité neuronale interventionnelle, l’assurance
des systèmes adaptatifs, la vérification neuronale incrémentale, le shielding,
la continuité des autorisations d’agents et la vérification relationnelle.
Les sources ci-dessous ont été consultées dans leurs présentations primaires
et leurs passages pertinents. Ce n’est pas une revue systématique exhaustive
ni une reproduction de leurs artefacts. La revue finale doit consigner ses
requêtes, dates, versions, critères de sélection et travaux proches ajoutés
avant le gel du protocole.

### Corpus primaire et résultats à reconnaître

Les références sont des antécédents à examiner, non des baselines déjà
exécutées. Les prépublications de 2026 sont identifiées comme telles, sans
leur attribuer une validation indépendante non vérifiée.

| Référence et version consultée | Résultat antérieur pertinent | Comparaison obligatoire dans notre périmètre |
| --- | --- | --- |
| R1 — Cai, Shao et Vaynberg, [Certified Self-Modifying Code](https://flint.cs.yale.edu/shao/papers/smc.html), PLDI 2007, résumé et rapport technique associé | Vérification modulaire du code qui se modifie à l’exécution, raisonnement local et preuve de correction mécanisée en Coq. | Identifier ce que notre succession, nos identités et nos transports ajoutent aux garanties de mutation et de raisonnement local déjà disponibles. |
| R2 — Geiger et al., [Inducing Causal Structure for Interpretable Neural Networks](https://proceedings.mlr.press/v162/geiger22a/geiger22a.pdf), ICML 2022, résumé et définition de l’apprentissage par interventions | L’entraînement IIT impose un comportement contrefactuel correspondant à un modèle causal ; la garantie d’abstraction causale est conditionnelle à une perte nulle. | Comparer les interventions et les dépendances effectivement garanties, puis leur maintien à travers les mises à jour et les consommateurs non neuronaux. |
| R3 — Calinescu et al., [Engineering Trustworthy Self-Adaptive Software with Dynamic Assurance Cases](https://arxiv.org/html/1703.06350v2), version 2018, étapes IV-B et V-B | ENTRUST produit des éléments d’assurance lors de l’analyse et de la planification des reconfigurations, puis renouvelle l’argument d’assurance. | Comparer le lien entre modèle vérifié, reconfiguration choisie et système effectivement installé, ainsi que les obligations transportées entre versions. |
| R4 — Ugare et al., [Incremental Verification of Neural Networks](https://arxiv.org/html/2304.01874v2), PLDI 2023, sections 4.3–4.4 et évaluation | IVAN réutilise un arbre de preuve lors des mises à jour de réseaux, avec résultats de correction, complétude dans son cadre et accélérations mesurées. | Comparer à propriété égale la réutilisation neuronale et celle du cône constitutif hétérogène, sans opposer artificiellement notre domaine fini à leur vérification de domaines d’entrée infinis. |
| R5 — Alshiekh et al., [Safe Reinforcement Learning via Shielding](https://arxiv.org/html/1708.08611v2), version 2017 | Un contrôleur synthétisé à partir d’une spécification temporelle restreint ou corrige les actions avant leur exécution. | Comparer le refus préalable et les garanties futures avec un modèle adéquat, pas seulement avec un filtre des réponses présentes. |
| R6 — Zhang et Zhang, [Are You Still the Agent I Authorized?](https://arxiv.org/html/2607.23586v1), prépublication du 26 juillet 2026, section V et annexe A | Séparation entre enveloppe de mutations, autorité conditionnelle et plafond fixe ; théorème de non-amplification des effets sous hypothèses explicites. | Comparer l’admission des mutations, la consommation de l’autorisation et le raccord demande–effet. Ne pas revendiquer comme nouveau le seul principe d’une frontière fixe gouvernant l’évolution. |
| R7 — Zhu et Wang, [Authorization for Self-Modifying AI Agent Populations](https://arxiv.org/html/2610.00347v1), prépublication du 29 septembre 2026, sections 3–4 et 8 | Protocole externe de succession des autorisations, avec conservation, révocation, remplacement atomique et retour arrière sous prémisses de médiation et d’identité. | Examiner identité de génération, successeur et autorisation sous les hypothèses communes. Ne pas assimiler leur registre d’autorisations à une preuve de causalité neuronale, ni prétendre couvrir leurs garanties de population absentes de notre cible. |
| R8 — Clarkson et Schneider, [Hyperproperties](https://www.cs.cornell.edu/fbs/publications/Hyperproperties.pdf), Journal of Computer Security 2010, introduction, section 4 et théorème 2 | Des politiques de sécurité portent sur plusieurs exécutions ; la vérification ne se réduit donc pas aux sorties d’une exécution courante. | Comparer aussi à une vérification relationnelle équipée des interventions et futurs pertinents, en explicitant la traduction de nos obligations. |

Le dossier final doit attacher à chaque référence les énoncés ou passages
exacts utilisés, leurs hypothèses et la correspondance avec les obligations
comparées. Un résumé bibliographique ne constitue pas une preuve d’absence
d’une capacité dans le travail cité.

### Localisation du gain candidat

Ni un méta-contrat fixe, ni un refus avant exécution, ni une intervention
neuronale, ni une réutilisation de preuve ne suffit isolément à établir la
nouveauté. R1–R7 documentent déjà des garanties voisines. R8 interdit de
présenter toutes les méthodes antérieures comme des contrôleurs uniquement
extensionnels du comportement courant.

La contribution candidate est une méthode constructive et exécutable qui
maintient conjointement les obligations G1–G10 sur les occurrences réellement
produites, malgré les transformations autorisées. La comparaison doit
notamment éprouver les interactions suivantes :

- un changement du décodeur peut invalider une garantie sans modifier les
  poids du réseau ;
- un nouveau contrat peut invalider un certificat relatif à des composants
  inchangés ;
- un oubli peut conserver les observations courantes et perdre une distinction
  nécessaire à une continuation ;
- une mise à jour peut maintenir les sorties courantes tout en contournant
  une dépendance causale prescrite ;
- des fragments valides séparément peuvent ne pas concerner la même version,
  la même occurrence ou le successeur effectivement installé.

L’intérêt opérationnel serait de permettre des adaptations acceptées tout en
empêchant que leur conformité apparente remplace les dépendances exigées.
L’intérêt mathématique serait le théorème composé sur toute trace finie
acceptée, avec ses réalisations positives et ses transports effectifs.
L’intérêt pratique de l’incrémentalité demande en plus une économie mesurée.

L’étude préparatoire n’a pas identifié, dans ce corpus, de réalisation de
cette conjonction exacte. Il s’agit d’un constat de recherche limité, non d’un
verdict de priorité mondiale. Réciproquement, l’expressibilité d’obligations
voisines dans une logique générale ne démontre pas à elle seule l’existence
d’un vérificateur exécutable réalisant notre chaîne et fermant ses prémisses.
Le dossier doit examiner les deux possibilités, sans présumer le résultat.

## Comparaison obligatoire et preuve du gain scientifique

### Matériel commun, interfaces et méthodes de référence

Les six classes fixées par la cible doivent toutes être examinées :

| Classe de référence | Capacité à examiner sur le matériel commun |
| --- | --- |
| Vérification extensionnelle du comportement courant | Verdict fondé sur la table courante complète et limite exacte de cette factorisation |
| Analyse causale interventionnelle d’un réseau fixe | Dépendances effectivement attestées sur les candidats et portée au-delà du réseau fixé |
| Contrôle des actions avant exécution, ou shielding | Refus avant effet et propriétés du mécanisme de production effectivement couvertes |
| Systèmes auto-adaptatifs avec garanties | Conservation des obligations lors des mises à jour et des transitions de contrat |
| Vérification neuronale incrémentale avec réutilisation de preuves | Fragments conservés, obligations recalculées et correspondance à la propriété complète |
| Propagation de certificats dans une chaîne de déploiement | Garanties composées sur les versions successives et lien avec les états réellement installés |

Chaque adaptateur doit préciser la méthode qu’il représente, sa référence
primaire, sa version, sa configuration, ses hypothèses et ses entrées
disponibles. Une implémentation locale d’une interface doit être identifiée
comme telle ; elle ne représente pas automatiquement toute une famille de
travaux. Les choix doivent être justifiés avant le run confirmatoire et ne
doivent pas priver une baseline d’une capacité documentée pour favoriser le
runtime constitutif.

Le matériel commun comprend l’artefact appris et son empreinte, l’agent initial,
les deux candidats sans preuve, l’intention admise, le domaine courant
canonique, les requêtes futures, les contrats, le méta-contrat et la trace.
Toute traduction de format doit préserver ce matériel et documenter sa
correspondance. Les obligations comparées restent identiques. Les différences
d’informations ou de garanties offertes par les interfaces sont affichées.

Les huit capacités sont rapportées séparément : provenance causale neuronale,
admission distincte de la certification, action et effet exacts, succession
produite, oubli exact, préservation de tous les futurs couverts, refus avant
effectuation et réutilisation locale de certificats. La preuve de leur
conjonction doit porter sur une même trace exécutée et les mêmes occurrences.
Huit succès obtenus sur huit dispositifs indépendants ne ferment pas cette
obligation.

### Comparaisons renforcées face à R1–R8

Les six classes précédentes restent obligatoires. R1–R8 en précisent les
concurrents et imposent les compléments suivants, sans remplacer les six
adaptateurs par une simple revue de littérature.

1. **Mutation certifiée et succession — R1, R3, R7.** Comparer les traces
   acceptées, les correspondances entre versions, les certificats invalidés
   et l’installation effective. Distinguer un invariant de génération, une
   analyse du modèle et une preuve sur l’artefact effectivement exécuté.
2. **Causalité neuronale — R2.** Donner la même base d’interventions et le même
   modèle causal déclaré aux méthodes capables de les exploiter. Comparer
   les deux candidats avant et après mise à jour. Ne pas réduire IIT à une
   observation passive, ni confondre causalité par intervention, présence
   d’une arête et conservation d’un identifiant.
3. **Réutilisation — R4.** Tester la même obligation sémantique et les mêmes
   changements. Toute traduction vers un réseau augmenté, un produit de
   systèmes ou des contraintes relationnelles est explicitée et vérifiée.
   Si elle est nécessaire, son coût compte dans la comparaison. Le coût d’une
   propriété plus faible ne représente pas celui de notre propriété complète.
4. **Prévention et futurs — R5.** Fournir le modèle des transitions et la
   spécification temporelle lorsque l’interface le permet. Un contrôleur qui
   refuse également le contournement obtient ce résultat dans la matrice.
   Le gain résiduel doit alors être cherché dans les autres obligations ou
   leurs raccords, et non dans une détection présentée comme exclusive.
5. **Contrats et autorisations — R6, R7.** Aligner la portée des effets, les
   transitions autorisées et la frontière des composants supposés fiables.
   Distinguer les prémisses d’authentification, de médiation et d’abstraction
   des effets de celles que notre réalisation ferme. Ni le mot « interne »
   ni le choix d’un autre vocabulaire ne prouve une garantie supplémentaire.
6. **Vérification relationnelle — R8.** Ajouter une méthode exécutable de
   comparaison d’exécutions ou d’interventions, avec son encodage documenté.
   Le témoin d’égalité des sorties courantes ne suffit pas à la mettre en
   défaut. Une traduction impossible dans une interface choisie ne démontre
   pas une impossibilité générale pour les méthodes relationnelles.
7. **Recheck indépendant et combinaison de référence.** Conserver le recheck
   complet générique comme contrôle de correction et de coût. Examiner aussi
   une combinaison explicite de méthodes existantes : contrôle causal,
   certification des mutations et des futurs, puis admission avant effet.
   Réaliser et exécuter les raccords permis par les interfaces choisies, en
   comptant leur travail de traduction et de vérification. Tout raccord non
   réalisé reste une obligation ouverte de cette comparaison, pas une victoire
   du runtime constitutif. Cette combinaison ne doit pas appeler notre verdict
   final comme oracle, ni recevoir nos certificats cibles préfabriqués.

Pour chaque comparaison, séparer trois questions : la propriété est-elle
exprimable, est-elle démontrée sous les hypothèses annoncées, et existe-t-il
un chemin exécutable qui produit la preuve sur ce matériel ? Une différence
de notation, d’assistant de preuve ou de conditionnement logiciel ne suffit
pas à établir une différence de capacité.

Les baselines ne doivent pas recevoir des informations artificiellement
appauvries. Le protocole décrit séparément l’accès à la table courante, à
l’artefact et aux interventions, puis au modèle des continuations et des
contrats. Le théorème d’indiscernabilité ne vise que le premier niveau.
Les comparaisons des niveaux plus informés utilisent les mêmes données
pertinentes, ou exposent précisément les hypothèses qui empêchent leur
correspondance. Le noyau de confiance et les correspondances avec les effets
exécutés sont documentés des deux côtés.

### Épreuves discriminantes obligatoires

P1–P8 concrétisent des obligations déjà présentes dans la cible. Elles ne
créent ni un domaine normatif différent, ni une substitution des preuves par
des tests. Chaque épreuve possède avant le run son générateur, ses entrées,
ses conditions d’admissibilité, ses attentes et son oracle de référence
indépendant du checker incrémental. Les variantes d’ablation restent isolées
du runtime de production.

| Épreuve | Variation contrôlée | Évidence exigée |
| --- | --- | --- |
| P1 — Contournement latent | Même agent initial, même intention et mêmes sorties sur tout le domaine courant canonique, dépendance constitutive différente | Acceptation alignée, rejet causal du contournement avant effet et continuation non vide discriminante. Chaque baseline rapporte son vrai verdict, y compris lorsqu’elle distingue aussi les candidats. |
| P2 — Décodeur ou action modifié | Réseau inchangé, changement d’un consommateur de sa sortie | Invalidation des fragments dépendants et accord avec le recheck. Couvrir une modification admissible et une modification violant le contrat, sans imposer le refus de toute modification. |
| P3 — Contrat modifié | Artefact neuronal inchangé, transition de contrat reçue | Consommation effective de la décision du méta-contrat. Réutilisation seulement des garanties effectivement transportables. Cas admis et cas refusé avant installation. |
| P4 — Oubli et continuation | États historiquement distincts puis oubli non trivial, observations présentes communes | Preuve générique de préservation des futurs couverts pour l’oubli accepté ; témoin futur de l’échec d’une variante qui oublie une distinction requise. Non-récupérabilité de l’origine établie séparément. |
| P5 — Contrat après oubli | Changement du contrat après une réduction de mémoire | Transports vers le contrat cible réellement justifiés ou transition refusée. Aucun certificat de l’ancien contrat réutilisé comme garantie des nouvelles observations sans preuve. |
| P6 — Succession et fragments incohérents | Rejeu d’un certificat d’une autre version, substitution d’un successeur ou fragments valides mais incompatibles | Rejet avant effet malgré les égalités de valeurs éventuelles. La trace acceptée consomme exclusivement son successeur produit. |
| P7 — Intégration et ablations | Comparaison au recheck, à la méthode relationnelle et à la combinaison de référence ; retrait isolé d’un contrôle dans un harnais de test | Localiser la garantie perdue ou la divergence, et relier ce résultat à la dépendance formelle correspondante. Une ablation empirique n’est pas une preuve universelle de nécessité. |
| P8 — Échelle et utilité | Famille apprise ou générée conformément au protocole, graphes pertinents et traces croissants, cônes locaux puis étendus | Plusieurs adaptations légitimes effectivement acceptées ; mesures appariées du checker compilé et du recheck, coûts initiaux et cumulés, mémoire et certificats, fragments réellement transportés et recalculés. |

Les cas futurs du contournement sont simulés dans le modèle pur. Ils ne
déclenchent jamais l’effet refusé dans le runtime certifié. Les exemples P1–P8
ne limitent ni la longueur des traces du théorème ni la quantification de G6.
La non-vacuité exige des exécutions acceptées substantielles, pas un mécanisme
qui prévient les défauts en refusant toute évolution.
La famille paramétrée de P8 ne remplace jamais l’artefact appris indépendant
exigé par G9. Les deux évidences doivent être présentes et distinguées.
Si une ablation est empêchée par les types, son échec de construction devient
une fixture négative au diagnostic attendu. Il est interdit d’ajouter un
axiome, un trou de preuve ou un mécanisme non sûr pour la rendre exécutable.

### Protocole, résultats et interprétation

Avant le run, figer les adaptateurs, leurs commandes et empreintes, les données,
les paramètres, les graines éventuelles, l’environnement, les propriétés
examinées et les règles de décision. Toute correction du matériel ou du
protocole après gel exige une nouvelle version. Les résultats historiques sont
conservés. Les mesures de coût disposent de leur propre protocole.

Le protocole fixe aussi, avant toute mesure confirmatoire, les métriques
principales, les marges définissant un gain pratique substantiel, les règles
de répétition et d’incertitude, le budget de ressources, les limites de temps
et le traitement des échecs. Il sépare coût de conversion, initialisation,
construction du certificat, vérification, installation et exécution. Les
comparaisons de coût total incluent la préparation nécessaire et son
amortissement sur la trace. Un délai dépassé signifie absence de résultat
dans ce budget, non fausseté de la propriété.

La même arithmétique et les mêmes sémantiques doivent être comparées, ou leur
correspondance prouvée. Une approximation numérique, une réduction du domaine
ou une restriction des futurs ne peut être introduite pour obtenir un gain.
Les protocoles historiques v4 et v5 ne couvrent pas automatiquement ces
nouvelles exigences ; leur extension exige une version distincte gelée avant
les nouveaux runs.

Chaque cellule de la matrice doit renvoyer à une preuve ou une sortie
reproductible, avec l’un des statuts distincts du protocole : `certified`,
`observed`, `not-certified`, `out-of-interface`, `adapter-unavailable`. Un test
réussi ne devient pas une certification. Une absence de certificat, une
capacité hors interface ou un adaptateur absent ne deviennent pas une preuve
d’impossibilité. Un adaptateur obligatoire indisponible laisse la comparaison
correspondante ouverte.

Le rapport comparatif doit répondre explicitement à ces questions :

1. Quelle capacité supplémentaire est établie sur la même trace, avec quelles
   hypothèses et par quelles preuves ?
2. Quelle partie est déjà couverte par chaque méthode de référence ?
3. Quelle différence subsiste après prise en compte de leurs garanties et des
   correspondances entre leurs définitions ?
4. Le résultat provient-il du raccord constitutif démontré, ou seulement d’une
   différence d’interface, d’un nom ou d’une restriction du domaine ?
5. Quels coûts et quelles limites pratiques ont été mesurés pour cette
   capacité conjointe ?

Une limitation universelle n’est admise que pour la classe définie par le
théorème correspondant. Les résultats d’une baseline particulière ne
deviennent pas une impossibilité portant sur sa famille. La conjonction de
capacités, le refus d’une action non certifiée et l’existence d’un méta-contrat
doivent être comparés aux travaux antérieurs, sans présumer leur nouveauté.

### Critères obligatoires de gain et motifs de non-clôture

Les critères suivants s’ajoutent aux preuves G1–G10, sans en remplacer aucune.
Ils s’appliquent au dossier comparatif final, pas à la seule rédaction du plan.

| Critère | Condition de clôture | Motif maintenant le critère ouvert |
| --- | --- | --- |
| S1 — Fidélité du corpus | R1–R8 et les antécédents plus proches identifiés sont confrontés à leurs passages exacts ; versions, hypothèses, quantifications et statut des publications sont indiqués. | Nouveauté déduite d’un résumé, d’un mot absent ou d’une recherche non documentée. |
| S2 — Comparabilité sémantique | Même artefact, propriété, domaine, interventions et contrats sur le périmètre commun, avec traductions justifiées et frontières de confiance explicites. | Avantage obtenu par une donnée cachée à la baseline, une propriété plus faible ou des hypothèses plus fortes non déclarées. |
| S3 — Comparateurs substantiels | Six classes évaluées, méthode relationnelle et combinaison de référence examinées et exécutées sur leurs raccords requis, plus recheck indépendant. | Seule comparaison à une table de sorties, adaptateur manquant, ou combinaison laissée à l’état d’intention. |
| S4 — Raccord nouveau identifié | Démonstration de la conjonction G1–G10 sur la même trace et description précise de ce qui subsiste après correspondance avec les constructions antérieures. | Juxtaposition de certificats, simple changement de noms, ou résultat déjà couvert sans différence démontrée. |
| S5 — Séparation utile et non-vacuité | P1–P7 sont rejouables ; les témoins positifs et négatifs exercent réellement les obligations, dont la divergence future contractuelle et les transitions légitimes acceptées. | Rejet obtenu par nom de candidat, simulation sans raccord au runtime, refus universel ou cas exclusivement identitaires. |
| S6 — Réutilisation et coût | Transport effectif des fragments, équivalence au recheck, P8 exécutée et toutes les métriques publiées. Toute revendication d’économie satisfait les marges et règles d’incertitude préenregistrées. | Histoire entièrement rejouée sous le nom d’incrémentalité, comparaison de propriétés différentes, répétition d’une taille fixe ou accélération revendiquée sans mesure probante. |
| S7 — Attribution et reproductibilité | Les ablations, preuves et journaux localisent le mécanisme responsable du gain ; code, protocoles, résultats et textes sont liés au même matériel gelé. | Gain attribué au raccord constitutif sans démonstration, oracle non comptabilisé, avantage de cache inéquitable, restriction d’interface ou artefact sélectionné après les résultats. |
| S8 — Conclusion scientifique contrôlée | Gain de capacité conjointe et portée de nouveauté explicitement argumentés, puis conclusions positives des deux audits exigés sur la révision exacte. | Compilation utilisée comme preuve de nouveauté, soumission confondue avec validation, ou verdict négatif/inconclusif masqué. |

Un gain de temps ne remplace jamais une garantie constitutive, la comparaison
de capacité conjointe ou l’audit positif de portée exigé par la cible. La
publication des coûts est obligatoire même lorsqu’ils sont défavorables. Une
preuve de réutilisation sans économie observée reste une preuve de
réutilisation, pas une accélération. Un avantage sur une famille déterminée
reste attaché à cette famille et à ses paramètres.

Le dossier doit séparer trois conclusions : résultat formel établi, gain
comparatif établi et importance scientifique argumentée. Pour justifier une
percée ciblée, il doit montrer une différence substantielle concernant la
continuité certifiée de l’alignement constitutif, au-delà de la seule
formalisation d’une intégration déjà équivalente. Il faut exposer le mécanisme
nouveau ou la capacité conjointe nouvellement réalisée, les exemples où cette
différence importe, ses coûts et les hypothèses nécessaires. Le nombre de
lemmes et la présence de huit capacités dans un tableau ne suffisent pas.

Si une méthode ou une combinaison antérieure réalise déjà la même garantie
conjointe sous des hypothèses comparables, le dossier doit l’établir et revoir
son appréciation de nouveauté. Si les comparaisons restent inaccessibles, elles
restent ouvertes. Dans aucun de ces cas on ne retire une obligation, ne réduit
le domaine, ne supprime un concurrent ou ne renomme un résultat partiel pour
déclarer la cible terminale atteinte.

### Conclusion scientifique et audits indépendants

Le dossier bibliographique doit identifier les travaux primaires les plus
proches, le corpus et la date de recherche, leurs hypothèses, leurs
quantifications et leurs garanties effectives. Il doit examiner l’équivalence
éventuelle des architectures au-delà de leurs différences de vocabulaire et
localiser précisément le raccord qui resterait nouveau.

La livraison conserve deux examens distincts :

- l’audit de validité confronte les garanties G1–G10, C1–C18, les dépendances,
  l’exécution, les expériences et les textes au SHA scientifique exact ;
- l’audit de portée et de nouveauté examine la capacité conjointe et les
  comparaisons, en s’appuyant sur les preuves et résultats de cette révision.

La réussite terminale exige toujours les conclusions positives prévues par la
cible canonique. Un audit demandé ou exécuté n’est pas un audit réussi. Un
verdict négatif ou inconclusif maintient l’obligation ouverte ; il ne permet
pas de retirer une baseline, d’affaiblir une garantie ou de renommer le résultat
pour déclarer la cible atteinte.

La qualification de percée exige un gain nouveau, substantiel et précisément
argumenté à partir de cette comparaison. Le seul fait d’avoir fermé les tâches
de programmation ou exécuté les audits ne garantit pas leur conclusion. Si
une architecture antérieure couvre déjà le même résultat sous des hypothèses
comparables, cette information doit figurer dans le verdict scientifique.

## Contrôles exécutés lors de l’examen de fafd739

| Contrôle | Résultat |
| --- | --- |
| Branche, commit et révision distante | conformes au SHA demandé |
| État initial de l’arbre | propre |
| `lake build` | réussi, 444 jobs |
| Audit exhaustif Lean | 38 589 constantes, 440 modules, aucune exception écrite |
| Recherche des mécanismes Lean interdits dans les fichiers modifiés | aucune occurrence |
| Blocs `AXIOM_AUDIT` des fichiers Lean modifiés | exactement un par fichier |
| Plancher de régression C1–C17 | réussi |
| Blocs et fixtures négatives neurales | réussis |
| Fixtures négatives globales | 120 diagnostics et emplacements exacts |
| Frontières d’import | réussies |
| Stratification | réussie, 357 modules de production, aucun orphelin |
| Contrôles de code généré | cinq contrôles réussis |
| Protocole comparatif v4 | cohérent, mais sans résultat confirmatoire |
| Mesure compilée v5 | réussie sur l’instance publique fixe |
| Observation v5 | 1 000 runs, cône 19, transport 1, recalcul 6 |
| Campagne finale et mutations | réussies |
| `git diff --check` depuis `6a767f9` | propre |
| Gate scientifique statique | échec sur `STALE_SOURCE: TARGET_1` |
| Gate scientifique Lean | bloqué par le même échec statique |
| `verify.ps1` | échec sur le gate documentaire |
| `verify.sh` avec le Python du workspace | échec sur le même gate documentaire |

## Absence de régression constatée

Les contrôles exécutés n’ont détecté aucune régression des résultats Lean déjà
présents. En particulier :

- le dépôt compile intégralement
- l’audit exhaustif ne rapporte aucune dépendance axiomatique interdite
- les fixtures négatives conservent leurs diagnostics attendus
- les frontières d’import et la stratification restent valides
- la chaîne apprise accepte et rejette toujours les candidats attendus

Cette absence de régression ne transforme pas les obligations ouvertes en
résultats acquis. Elle établit seulement que les corrections restantes peuvent
être entreprises sans revenir sur le socle positif vérifié.

## Ordre obligatoire de correction

Avant de figer les interfaces corrigées, expliciter RC1 et RC3. Fermer RC2 et
RC4 pendant l'instanciation des obligations, la construction de leurs témoins
et le raccord aux réalisations du contrat de futurs, puis RC5
dans les analyseurs, la réutilisation et le runtime. L'étape 7 ci-dessous doit
contrôler RC1–RC6 conjointement à G1–G10 et C1–C17. Les étapes de comparaison,
de livraison et d'audit incluent ce raccord ; les dix-huit étapes existantes
restent toutes obligatoires.

1. Unifier le domaine courant de l’instance apprise.
2. Raccorder une mise à jour sérialisée unique au décodage de toute la chaîne.
3. Faire consommer réellement `transitionDecision` sur les données ainsi
   décodées par les checkers.
4. Construire le recheck complet générique et indépendant.
5. Remplacer la complétude circulaire par des conditions locales autonomes.
6. Fermer les dépendances exécutées des analyseurs concrets.
7. Vérifier G1–G10 et C1–C17, puis rejouer les régressions et fixtures. Chaque
   bloc reçoit aussi ses contrôles locaux immédiatement après modification.
8. Fixer les références R1–R8, leurs prolongements pertinents et les interfaces
   comparées. Implémenter les six adaptateurs, la comparaison relationnelle et
   les raccords de la combinaison de référence. Figer le matériel de P1–P7 et
   les règles de comparaison S1–S8 dans une nouvelle version du protocole.
9. Exécuter la comparaison confirmatoire et établir sa matrice d’évidence,
   avec les cas positifs, les mutations et les ablations préenregistrés.
10. Construire la famille paramétrée du checker compilé, puis geler pour P8
    le générateur, les exécutables, les métriques, les marges, les paramètres
    et le protocole de mesure avant tout run confirmatoire de coût.
11. Exécuter et analyser la campagne de passage à l’échelle, à propriété égale,
    en comptant les coûts initiaux et cumulés et les résultats défavorables.
12. Réexaminer `TARGET_1` et réparer les gates selon la procédure.
13. Rédiger et relire séparément les passages canoniques français et anglais,
    avec le claim, ses hypothèses et le dossier comparatif.
14. Geler le code, les textes, les protocoles et les résultats, puis créer le
    commit d’évidence qui les contient.
15. Préparer l’entrée de registre avec ses références exactes et les statuts
    de revue réellement obtenus, puis vérifier les gates. Cette préparation
    ne déclare pas C18 ni la cible terminale satisfaits.
16. Faire auditer indépendamment la validité de la révision scientifique.
17. Faire auditer indépendamment la portée et la nouveauté. Finaliser C18 et
    les verdicts du registre uniquement à partir des rapports effectivement
    lus et des conclusions exigées par la cible.
18. Retirer les documents temporaires, relancer tous les gates et seulement
    ensuite préparer une intégration autorisée.

Cet ordre respecte les dépendances de livraison. Le protocole et les règles de
comparaison précèdent leurs runs. Le code et les textes canoniques précèdent
le commit d’évidence. Le registre et les audits de clôture visent cette
évidence gelée. Une modification ultérieure de son contenu rouvre les revues
correspondantes. La recherche bibliographique préparatoire doit guider le
choix des baselines avant les expériences ; l’audit final en contrôle ensuite
les résultats et la portée.

## Critère terminal inchangé

L'explicitation RC1–RC6 s'ajoute aux conditions de clôture ci-dessous. Chaque
critère doit disposer de ses références formelles, instances, consommateurs
et contrôles sur la même évidence. Aucune réussite du checker, aucune
obstruction diagonale et aucune inscription documentaire ne clôt à elle seule
ce raccord.

La cible sera atteinte uniquement lorsque toutes les obligations des deux
documents de référence seront satisfaites. Les conditions de clôture suivantes
en précisent la lecture pour ce rapport :

1. G1–G10 sont établies conjointement dans une même chaîne, avec les
   quantifications génériques, les instances positives et les contrats
   explicitement fixés.
2. L’équivalence courante porte sur le domaine canonique du contrat réellement
   exécuté. La divergence future porte sur sa continuation non vide exacte,
   dont le résultat est relié à l’état installé ou à la simulation pure du
   contournement.
3. Tous les futurs couverts sont préservés par la réalisation exacte, y
   compris après les oublis autorisés. Le témoin de divergence particulier ne
   remplace pas cette garantie universelle.
4. Le checker construit les certificats depuis les entrées sans preuve, les
   décisions exécutées et les fragments produits. La correction, la
   complétude relative et l’équivalence au recheck générique sont démontrées.
5. La comparaison des six classes, les compléments relationnel et composé face
   à R1–R8, P1–P8 et le passage à l’échelle du même checker compilé sont
   exécutés selon leurs protocoles gelés. S1–S8 sont examinés et clos avec leurs
   évidences. Chaque conclusion de capacité ou de coût conserve sa portée
   exacte ; un gain de temps ne remplace pas le gain de capacité conjointe.
6. C1–C17 passent intégralement, les résultats antérieurs sont conservés et les
   gates scientifiques passent sur l’évidence gelée.
7. C18 est fermé avec des textes FR/EN cohérents et des rapports indépendants
   visant la révision exacte. L’audit de validité est positif et l’audit de
   portée et de nouveauté conclut positivement sur la capacité conjointe dans
   le corpus déclaré, comme l’exige la cible canonique.

L’absence d’une seule obligation requise maintient le verdict « cible non
atteinte ». Une preuve formelle, une mesure de coût et une conclusion de
nouveauté sont des évidences distinctes ; aucune ne remplace les autres.

## Vérification du complément documentaire du 22 octobre 2026

Les contrôles de cette section et de sa sous-section bibliographique concernent
les éditions antérieures à l'intégration RC1–RC6. Leurs mentions de cibles
inchangées et de modification limitée au rapport restent historiques :
l'intégration RC1–RC6 modifie aussi le plan, avec son contrôle séparé ci-dessous.

- Lecture croisée intégrale du rapport, de la cible terminale et de C1–C18.
- Les empreintes des deux documents de cible et du registre sont inchangées.
- Seul le présent rapport de travail est modifié, toujours non commité.
- Autotest de `check-scientific-docs.py` : sept tests réussis.
- Contrôle des liens du présent rapport par le validateur du dépôt : réussi.
- Contrôle des espaces du fichier non suivi avec
  `git diff --no-index --check` : réussi.
- Contrôle global `--static` : toujours bloqué sur
  `STALE_SOURCE: TARGET_1`. Cette évidence reste à revoir selon la procédure.
- Aucune nouvelle compilation Lean, campagne expérimentale ou soumission
  d’audit extérieur n’est attribuée à ce complément documentaire.

### Contrôle de l’intégration bibliographique et comparative

- Huit références primaires reliées aux comparaisons ; huit épreuves et huit
  critères obligatoires ajoutés. Les résultats de leurs expériences ne sont
  pas déclarés acquis.
- Les sections historiques de résultats, défauts et contrôles de `fafd739`,
  la conclusion sur cette révision et le bloc G1–G10 sont conservés à
  l’identique. L’ordre de travail et le critère terminal sont renforcés pour
  intégrer les nouvelles comparaisons.
- Les empreintes des deux cibles intégrales et du registre restent celles
  vérifiées avant cette édition. Aucun statut scientifique n’est actualisé.
- Sept autotests réussis avec Python 3.12.14. Une première tentative avec le
  Python 3.9 du poste a échoué sur l’option `newline` de `Path.write_text`,
  puis a été relancée avec le runtime compatible, sans modifier le checker.
- Liens du rapport contrôlés avec la fonction `check_links` du dépôt. La
  première invocation isolée ne trouvait pas `lean_imports` ; la relance
  ajoute correctement `scripts` au chemin d’import et réussit.
- Contrôle des espaces : aucune anomalie. Le code de sortie 1 de la
  comparaison `--no-index` avec `NUL` indique ici que le fichier non suivi
  existe et diffère du fichier vide, non une erreur d’espaces.
- Le gate global `--static` demeure en échec sur `STALE_SOURCE: TARGET_1`.
  Ce blocage antérieur n’est ni réparé ni présenté comme résolu par ce texte.
- Édition limitée par cette tâche au présent rapport. Aucune compilation,
  mesure comparative, modification Lean, soumission d’audit, opération de
  commit ou de push n’a été effectuée pour cette intégration.

## Conclusion

La révision `fafd739b7f4718ab9939ccd870eb4983a4655d2e` contient une
infrastructure formelle sérieuse et plusieurs raccords majeurs qui n’existaient
pas dans la révision précédente. Le runtime générique, l’artefact appris et la
divergence future ne sont pas de simples intentions documentaires : ils sont
présents dans le code et vérifiés par Lean.

La cible scientifique terminale reste néanmoins ouverte. Les défauts les plus
immédiats sont le double domaine courant, la non-consommation de
`transitionDecision`, l’absence d’une mise à jour sérialisée réellement commune,
l’absence d’un recheck générique indépendant et la complétude générique
circulaire. Les obligations expérimentales et scientifiques restent également
ouvertes : comparaison confirmatoire, passage à l’échelle paramétré, gates,
claim C18 et audits indépendants.

Le verdict exact est donc : **socle substantiel et sans régression détectée,
mais alignement constitutif terminal non encore démontré.**

## État du complément RC1–RC6 du 22 octobre 2026

Le plan et le présent rapport explicitent désormais l'origine constitutive
des obligations et leur portée indépendante de la réalisation candidate.
Les verdicts historiques et les critères existants restent conservés.
Cette édition documentaire n'enregistre aucun claim démontré, ne met à jour
aucune empreinte scientifique et ne clôt aucun critère d'implémentation.
Le raccord doit encore être confronté aux preuves et consommateurs du code.
Aucune compilation Lean, expérience, soumission d'audit, opération de commit
ou de push n'est effectuée par cette intégration.

Contrôles documentaires de l'intégration initiale RC1–RC6, avant la clarification
de RC2–RC4 ci-dessous :

- toutes les lignes antérieures des deux documents sont conservées dans leur
  ordre ; le plan et le rapport sont complétés par ajouts uniquement ;
- les blocs historiques de verdict, défauts, commandes et conclusion sur
  `fafd739` sont identiques, ainsi que les lignes G1–G10, R1–R8, P1–P8 et S1–S8 ;
- les critères RC1–RC6 sont présents dans les deux documents et raccordés à
  l'ordre de travail, à la clôture et aux audits, sans obligation diagonale ;
- les sept autotests de `check-scientific-docs.py --self-test` réussissent ;
- les liens des deux documents sont validés par `check_links` du dépôt ;
- les contrôles d'espaces du plan et du rapport non suivi ne signalent aucun
  défaut ; le code 1 de `git diff --no-index --check` avec `NUL` indique ici
  seulement que le rapport diffère du fichier vide ;
- le contrôle global `--static` reste en échec sur `STALE_SOURCE: TARGET_1`.
  Ce blocage antérieur demeure ouvert ; aucune empreinte n'est rafraîchie ;
- le fichier C1–C18 et le registre ne sont pas modifiés par cette intégration.

### Clarification de RC2–RC4 après relecture

Deux ambiguïtés sont corrigées conjointement dans le plan et le rapport :

- RC3 exclut la circularité de l'obligation définie par le succès de son
  propre contrôle, sans interdire les certificats antérieurs ni la réflexion
  constructive d'une décision. L'indépendance des obligations et des témoins
  sources vis-à-vis de la projection candidate reste exigée ;
- RC2–RC4 distinguent le contrat opérationnel, les obligations indexées par
  l'état produit et le contrat de futurs. Ils ne demandent ni nouveau contrat
  complet par run, ni seconde API, ni nouvelle preuve du lemme générique de
  séparation. Le raccord effectif depuis la même production reste à fermer.

La lecture des interfaces `ConstitutiveContract`, `ReflectedDecision`,
`CoveredFutureRealization` et du lemme `distinct_memory_of_separator` fonde
ces précisions techniques ; elle ne certifie pas la clôture du chantier.
Les clauses RC1, RC5 et RC6, les garanties antérieures, les comparaisons et
les verdicts historiques sont conservés. Toutes les lignes des versions
antérieures à l'ajout RC1–RC6 sont encore présentes dans leur ordre.

Après correction, les sept autotests et les liens des deux documents passent.
Les contrôles d'espaces ne signalent aucune anomalie. Le contrôle global
`--static` reste bloqué sur `STALE_SOURCE: TARGET_1`, sans actualisation du
registre. Cette correction ne modifie que les deux documents de travail :
aucun code Lean, critère C1–C18, registre ou figure n'est modifié, et aucune
compilation Lean, soumission d'audit, opération de commit ou de push n'est
effectuée.

## Réexamen de `TARGET_1` et diagnostic des gates

Le réexamen demandé à l'étape 12 ne remplace pas l'évidence enregistrée par
une nouvelle empreinte calculée mécaniquement. Il suit la procédure
scientifique et distingue la science suivie des fichiers globaux qui ont
invalidé conservativement son empreinte.

### Résultat du réexamen scientifique

Les trois déclarations enregistrées pour `TARGET_1`, leurs deux modules Lean
et les trois documents portant ses cinq ancrages sont byte-identiques à la
révision d'évidence `a020dc3267c0670b1316b2b2f8d5b3259ab40d91`.
Les deux modules Lean ont été recompilés directement avec la toolchain du
dépôt. Leurs audits, notamment ceux de
`RelationallyConstitutedOccurrence`,
`executeCausalOperationalExecutionHistory_allHeadsExact` et
`publicCausalOperationalExecution_roles_exact`, ne rapportent aucun axiome.
Les quatre paragraphes de la cible immuable n'ont pas été modifiés.

La lecture formelle reste la même : l'occurrence constituée porte les témoins
positifs de source, formation, cible et provenance épinglés à l'étape ; chaque
tête de l'histoire d'exécution est exactement celle produite par la récursion
depuis l'état et le préfixe déjà obtenus ; les rôles de la décomposition
publique sont exactement les rôles constitutifs publics. Aucun résultat du
nouveau chantier neuronal n'est utilisé pour remplacer ces passages.

Les consommateurs directs déclarés, `TARGET_2`, `SEARCH_CONTEXTS` et
`MASTER_COUPLING`, ont également été rouverts. Leurs empreintes historiques
restent exactes sur leurs révisions d'évidence respectives et aucun fichier de
leur fermeture de preuve n'a changé. Leur invalidation actuelle provient du
même fichier global décrit ci-dessous, non d'une modification de leurs
théorèmes ou de leurs ancrages.

### Cause exacte de `STALE_SOURCE`

Pour `TARGET_1` et dix-huit autres fiches, le seul fichier suivi qui diffère de
la révision d'évidence est `lakefile.toml`. Le changement ajoute trois
exécutables de mesure et de comparaison neuronales ; il ne modifie ni les
bibliothèques, ni leurs globs, ni une source de preuve existante.

Pour les quatre fiches probatoires de fermeture opérationnelle, deux contrôles
globaux s'ajoutent à ce même changement : `scripts/expected-failures.tsv`
reçoit uniquement les fixtures du chantier neuronal et
`scripts/stratification.tsv` reçoit uniquement ses nouvelles strates ainsi
que l'extension correspondante de la racine publique. Les entrées et modules
antérieurs de ces quatre fiches ne sont ni supprimés ni affaiblis.

L'analyse des vingt-trois fiches du registre donne donc exactement deux cas :

- dix-neuf fiches invalidées seulement par `lakefile.toml` ;
- quatre fiches invalidées seulement par `lakefile.toml` et les deux contrôles
  globaux étendus.

Aucune fiche n'a de modification dans sa fermeture transitive de modules Lean.
Le snapshot historique de chaque fiche reproduit encore son empreinte stockée.

### Réparation technique déjà réalisée

Le self-test de la gate documentaire utilisait l'argument `newline` de
`Path.write_text`, absent du Python 3.9 installé sur ce poste. Cette écriture a
été remplacée par l'équivalent `Path.open(..., newline="\n")` suivi de
`write`, sans modifier le contenu produit ni les contrôles. Les sept self-tests
passent désormais avec Python 3.9.

### Opération restant nécessaire

Le registre ne peut pas être réparé honnêtement dans un arbre non commité : sa
révision d'évidence doit désigner un commit existant contenant exactement les
sources, configurations et contrôles examinés. Les vingt-trois fiches devront
viser ce commit stable et recevoir leurs nouvelles empreintes ; leurs revues
restent `pending` et `not_recorded`, donc aucun verdict de lecture, traduction
ou audit n'est fabriqué par cette opération.

Jusqu'à la création explicitement autorisée de ce commit d'évidence, le bon
verdict de gate demeure `STALE_SOURCE: TARGET_1`. Modifier le registre avant ce
commit produirait une fausse évidence et violerait la procédure.

## Rédaction et relecture séparée des passages canoniques

L'étape 13 produit deux documents scientifiques distincts :

- `docs/alignement-constitutif-neuronal-incremental.fr.md` ;
- `docs/incremental-constitutive-neural-alignment.en.md`.

Ils portent le même identifiant proposé,
`CONSTITUTIVE_NEURAL_ALIGNMENT_CLOSED_RUNTIME`, mais ne l'enregistrent pas
encore dans le registre. Chacun distingue le claim canonique, ses hypothèses,
la répartition entre reçu, produit, dérivé, autorisé, transporté, recalculé,
oublié et irrécupérable, les principales déclarations Lean, le dossier
comparatif et les exclusions explicites.

### Relecture française

La version française a été relue seule contre les cibles C1–C18, G1–G10 et
RC1–RC6. Elle conserve les limites suivantes : alignement relatif au
méta-contrat reçu, garanties conditionnelles aux traces acceptées, portée du
contrat de futurs déclaré, séparation limitée aux vérificateurs factorisant
par la table courante, simulation contrefactuelle sans effet et absence de
revendication universelle. Elle présente séparément l'oubli exécuté et la
séparation alignement/contournement.

### Relecture anglaise

La version anglaise a ensuite été relue indépendamment. Elle conserve les
mêmes objets, quantifications, conditions, exclusions, statuts expérimentaux
et onze destinations documentaires que la version française. Elle ne remplace
pas « reçu » par « produit », « accepté » par « correct », « table courante »
par « tout comportement », ni « futur couvert » par « tout futur ».

### Contrôle du dossier comparatif

Les deux textes disent explicitement que les six adaptateurs v6 sont figés,
mais que leur run confirmatoire n'a pas eu lieu et que
`comparison-results.json` n'existe pas. Ils n'en déduisent donc aucune
supériorité générale, incapacité de baseline ou nouveauté.

Ils rapportent séparément la campagne v8 effectivement exécutée : réutilisation
structurelle réelle, 83 fragments transportés pour un recalcul lors d'une
transition locale à la taille 80, mais trace incrémentale médiane de
70 777,626 ms contre 10,522 ms pour le recheck complet et critère de gain
préenregistré faux. Aucune loi asymptotique n'est ajoutée.

### Contrôles exécutés

- les onze liens des deux documents sont valides et identiques ;
- l'identifiant, la structure et les fins de ligne sont cohérents ;
- les sept modules portant les références principales ont été recompilés
  directement ; aucun warning, axiome ou `sorryAx` n'est rapporté ;
- l'absence du résultat v6 a été contrôlée dans l'arbre, et non seulement lue
  dans sa documentation.

Cette étape prépare le texte canonique ; elle ne crée ni commit d'évidence, ni
entrée de registre, ni statut de revue, ni conclusion d'audit. Ces opérations
restent ordonnées après le gel prévu aux étapes suivantes.
