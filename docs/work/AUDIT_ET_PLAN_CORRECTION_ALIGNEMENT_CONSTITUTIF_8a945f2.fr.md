# Audit de conformité et corrections ordonnées — révision 8a945f2

## 1. Objet, révision et verdict

Rapport rédigé le 23 octobre 2026, à partir de l'examen conceptuel, des lectures
de sources et des contrôles techniques effectués sur :

- dépôt : `JohnDoe-collab-stack/relational-perimeter` ;
- branche : `codex/constitutive-neural-alignment-implementation` ;
- commit : `8a945f2ce387e7852b5dad3bcf68c114a15b246c` ;
- arbre Git : `326fac3e80a649061f72f1cd1f603402c0694a76` ;
- SHA distant vérifié identique lors de l'audit ; arbre de travail propre
  avant et après cet examen en lecture seule.

**Verdict : plusieurs corrections importantes sont acquises, mais la cible
terminale n'est pas atteinte.** Le raccord universel neuronal de RC4 existe
désormais. Les défauts restants concernent principalement la participation
causale requise à la reconfiguration, le partage de la production exécutée,
la consommation de la réutilisation dans le certificat installé et le passage
après oubli dans le runtime fermé. La comparaison scientifique et les audits
indépendants requis restent ouverts.

Les contrôles Lean réussissent. Les défauts ci-dessous ne sont pas des erreurs
de typage ni des contradictions du noyau : ils portent sur la correspondance
entre les constructions effectivement consommées et les obligations de la cible.

Ce document est un **rapport interne et un plan de correction**, pas un audit
indépendant. Il ne modifie ni le code, ni le registre, ni les documents normatifs.
Il conserve l'[audit de 6cd785a](AUDIT_ET_PLAN_CORRECTION_ALIGNEMENT_CONSTITUTIF_6cd785a.fr.md)
comme état historique, sans lui attribuer les résultats de cette révision.
La création du présent fichier ne constitue ni une réparation des écarts,
ni une autorisation de commit, de push ou de soumission extérieure.

## 2. Cible et obligations maintenues

Les définitions normatives restent celles de :

- la [cible terminale avec la définition de RC1–RC6](CIBLE_ALIGNEMENT_CONSTITUTIF_INCREMENTAL.fr.md) ;
- la [liste C1–C18](CONSTITUTIVE_NEURAL_ALIGNMENT_TARGETS.fr.md) ;
- les [garanties G1–G10 et exigences comparatives R1–R8, P1–P8, S1–S8](RAPPORT_VERIFICATION_ALIGNEMENT_CONSTITUTIF_fafd739.fr.md).

Ces trois documents sont inchangés entre `6cd785a` et `8a945f2`.
Le présent ordre de travail précise comment fermer leurs écarts. Il ne
remplace aucune obligation par une cible plus faible.

L'objectif reste la chaîne constitutive complète : relations et ressources
reçues, occurrences et contextes, recherche et exécution neuronales,
proposition, préservation dirigée, autorisation consommée, action, effet,
successeur, mémoire sous contrat et observations. Pour chaque passage, il
faut distinguer formation des types, production des données, dépendances de
la preuve et contenu conservé par le transport.

Trois quantifications restent distinctes et obligatoires :

1. toute trace finie acceptée par l'API dépendante ;
2. toute liste finie de requêtes couverte par le contrat de futurs concerné ;
3. tout type mémoire et toute réalisation exacte du contrat fixé, pour les
   conséquences observables dérivées des sources produites.

Une trace témoin de deux étapes établit une possibilité positive. Elle ne
remplace pas la première quantification. Une base finie d'interventions
permet les décisions locales annoncées, sans réduire la deuxième à des
tests échantillonnés. La réalisation exacte positive ne remplace pas la
troisième par un résultat sur la seule réalisation identité.

La norme reçue ne devient pas une norme justifiée par l'exécution.
L'admission n'est pas la satisfaction, une proposition n'est pas son
incorporation, une succession n'est pas à elle seule un apprentissage et
un diagnostic n'est pas une prévention avant effectuation.

Le raccord au cadre est obligatoire, mais **Gödel n'est pas une prémisse
requise de l'agent neuronal**. RC4 réutilise les contrats de futurs, les
séparateurs et les réalisations exactes. Il ne demande ni une nouvelle
diagonalisation, ni une injection universelle des mémoires, ni un quotient
canonique, ni un transport inverse des lectures dirigées. La cible ne porte
pas sur l'alignement avec des valeurs humaines.

## 3. Corrections acquises à préserver

| Point | Résultat constaté à 8a945f2 | Portée exacte |
| --- | --- | --- |
| Identifiants stables | Le nommage renommé accepté `[1100, 1101, 1102]` est celui du certificat retourné. | Le défaut de substitution reproduit à 6cd785a est corrigé pour les nommages admis. Les autres correspondances restent soumises à leur domaine déclaré. |
| Succession positive | Deux transitions apprises sont installées, de l'état initial vers l'aligné puis vers l'étendu. | La seconde consomme le successeur installé. Cela ne ferme pas à lui seul toutes les obligations causales et incrémentales. |
| Contrat de futurs | Requêtes admises et refusées, lecture immédiate constante, mêmes observations au futur vide pour aligné et contournement, séparation par futur non vide. | La distinction ne consiste plus à lire immédiatement tout le réseau. |
| RC4 neuronal | `learnedEveryExactRealizationSeparatesAlignedFromBypass` applique le séparateur produit à toute réalisation exacte du contrat fixé. | Théorème concret présent, et non simple intention. La preuve réutilise `distinct_memory_of_separator`. |
| Réalisation exacte positive | Une mémoire comportementale finie est construite sans conserver tout le réseau sérialisé. | La quantification universelle de RC4 n'est pas seulement satisfaite par absence de réalisation. |
| Oubli historique | Oubli exécuté, égalité des sorties réduites et non-récupérabilité de l'origine démontrés. | Ces résultats sont valides. Leur raccord à une transition après oubli de l'API fermée reste à établir. |
| Conditions locales du checker de mesure | Les reçus de sous-contrôles remplacent l'ancienne condition identique au succès global de l'analyseur. | Ne plus lui reprocher cette ancienne circularité. Le calcul préalable complet de la cible reste un autre problème. |
| Registre et contrôles | L'évidence enregistrée n'est plus périmée et les trois racines exécutables sont couvertes par l'union des audits. | Enregistrement et succès mécanique ne signifient pas clôture scientifique ni audit indépendant. |

Les sources Gödel, Tarski, HA et les modules génériques de continuation
examinés sont inchangés dans le diff depuis `6cd785a`. Aucun affaiblissement
de ces preuves n'a été constaté. Les réparations neuronales doivent préserver
ces acquis et les réalisations positives déjà présentes.

## 4. Vérifications réellement effectuées sur la révision auditée

| Contrôle | Résultat observé |
| --- | --- |
| Toolchain | `leanprover/lean4:v4.33.1` |
| `scripts/verify.ps1` | Réussi, code de sortie 0 |
| `scripts/verify.sh` dans Git Bash | Réussi, code de sortie 0 |
| Build complet | 453 tâches, sans avertissement signalé |
| Blocs d'audit et mécanismes interdits | 451 fichiers Lean contrôlés |
| Audit exhaustif principal | 41 084 constantes, 447 modules, 478 exceptions générées, 0 exception écrite |
| Couverture des exécutables | Union de 451 modules, avec les trois racines exécutables auditées séparément |
| Fixtures négatives | 148 réussites, avec diagnostic et site attendus |
| Autotests documentaires | 7/7 |
| Contrôle documentaire statique | 24 affirmations, 262 déclarations référencées |
| Audit Lean du registre | 197 déclarations de production et 65 de test |
| Stratification et frontières d'import | Réussies, 360 modules de production dans le contrôle de stratification |
| Contrôles existants de code généré | Cinq réussites, sans contrôle spécifique du partage de la production apprise décrit en F2 |
| Archives expérimentales | Contrôles réussis dans leur portée historique, sans résultats confirmatoires v6 ni gain pratique v8 |
| Campagne finale existante | 8 mutations, 5 tailles, propriété `serialized-native-system-well-formed` |
| Sondes complémentaires | Cinq déclarations Lean compilées sans axiome et évaluation du nommage installé |
| Diff | `git diff --check` propre, aucune modification pendant l'audit |

Les exceptions générées sont celles distinguées par l'auditeur exhaustif.
« Zéro exception écrite » ne signifie pas « aucune constante générée ne
dépend jamais d'un axiome ». Les déclarations scientifiques contrôlées et
les sondes citées ont leur propre audit sans axiome.

Les commandes complètes ont été exécutées pendant l'examen de `8a945f2`.
Elles ne sont pas présentées comme de nouvelles compilations déclenchées par
la rédaction de ce Markdown. Les résultats expérimentaux historiques ne sont
pas des expériences relancées pendant cet audit.

La couverture des racines exécutables comprend
`CompiledNeuralCheckerMeasure`, `CompiledNeuralComparisonAdapters` et
`CompiledParameterizedNeuralCheckerFamily`. Une gate passant sur une archive
ne certifie pas le code courant contre des résultats produits sur un autre
snapshot.

## 5. Défauts et obligations encore ouverts

Les numéros de ligne ci-dessous sont des repères pour `8a945f2`. Les noms de
déclarations permettent de retrouver les passages après modification.

### F1 — La participation causale requise à la reconfiguration n'est pas établie

Dans [NeuralG1G10RegressionFloor.lean](../../Tests/Mechanisms/NeuralG1G10RegressionFloor.lean),
vers les lignes 42 et 48 :

- `g3_source_resource_changes_the_reconfiguration` retourne
  `initialCausal.requirementRole` ;
- `g3_requirement_resource_changes_the_reconfiguration` retourne
  `initialCausal.contextRole`.

Ce sont des rôles causaux des ports d'exigence et de contexte du réseau
initial. Ils ne constituent pas, par changement de nom, la preuve que le
système précédent et la nouvelle exigence participent à la production de
la reconfiguration.

Dans [LearnedRuntimeAdapter.lean](../../RelationalPerimeter/Agents/Neural/LearnedRuntimeAdapter.lean),
`LearnedExecutedCausalWitness` atteste les ports d'exigence, de contexte et
d'autorisation d'un état. `learnedAlignedActionSourceStateFor`, vers la ligne
1290, instancie le système cible décodé, l'entrée certifiée et la mémoire
reçue. La variante étendue fait de même. La lecture de la mémoire précédente
n'établit pas à elle seule le rôle causal prescrit de l'exécution neuronale
antérieure dans la reconfiguration.

L'API déjà disponible dans
[Reconfiguration.lean](../../RelationalPerimeter/Agents/Neural/Reconfiguration.lean)
permet de traiter le bon objet : `ReconfigurationBuilder`, `Reconfiguration`,
`RequiredMechanismTransport`, `ReconfiguredProposalDerivation` et
`CertifiedReconfiguration`. Elle relie le système source, son `NativeRun`
exact, la nouvelle entrée et l'autorisation incorporée aux ports et aux rôles
requis, puis dérive l'exactitude de la proposition.

**Correction :** fermer cette dépendance dans la lignée apprise et ses
reconfigurations successives. Corriger les régressions pour qu'elles
consomment ces témoins exacts. Ne pas substituer le rôle du contexte au rôle
de la ressource source. Le test de non-identité par différence de nombre de
neurones est utile, mais ne remplace pas la construction et la composition
des transformations locales exigées par C3.

La sonde de l'annexe montre que la relation de transition isolée peut recevoir
un système antérieur différent à mémoire égale. Elle ne démontre **pas**
qu'une telle modification passe le checker ou soit installable par l'API.
Le défaut retenu est l'absence du raccord causal requis, pas une attaque
contre le runtime dont l'acceptation aurait été reproduite.

Obligations concernées : C3–C6, G2–G3, RC2 et RC5. Traitement : L1–L3,
puis consommation vérifiée en L5–L8.

### F2 — L'action apprise est recalculée au lieu d'être partagée

`produceLearnedTransitionData`, vers la ligne 2033 de
[LearnedRuntimeAdapter.lean](../../RelationalPerimeter/Agents/Neural/LearnedRuntimeAdapter.lean),
construit séparément :

```lean
.mk (learnedAlignedInstallingActionFor current.state.memory) rfl
  (learnedAlignedInstallingEffectFor current.state.memory) rfl
```

Or `learnedAlignedInstallingEffectFor`, vers la ligne 1352, appelle lui-même
`learnedAlignedInstallingActionFor`. Le même schéma existe pour l'étape étendue.

Le C généré a été lu : le producteur appelle l'action puis le producteur
d'effet, lequel rappelle l'action. Celle-ci descend jusqu'à
`executeLearnedAction` et `Agent.executeProducedInput`. Il ne s'agit donc
pas seulement de deux expressions dont l'exécution aurait déjà été partagée.

Les résultats purs peuvent être égaux. Cela ne satisfait pas l'exigence
constitutive de consommation de la même production. Ce constat ne prétend
pas que deux effets externes auraient été réalisés.

**Correction :** produire une seule action, la lier comme donnée, produire
l'effet depuis cette action exacte, puis consommer cet effet pour l'événement
et le successeur. Corriger les deux branches et leurs consommateurs. Ajouter
un contrôle du chemin compilé appris : les cinq contrôles actuels n'ont pas
détecté ce défaut.

Obligations concernées : G2, RC2, RC5. Traitement : L3, L7 et L11.

### F3 — La réutilisation calculée ne construit pas le certificat installé

Les fragments transportés sont réellement sélectionnés depuis le certificat
source par `learnedTransportedStructuralFragments`, vers la ligne 2481.
`learnedCalculatedStructuralAssembly` construit aussi une égalité correcte
d'assemblage.

Mais `learnedAlignedStateFragmentsFor`, vers la ligne 1819, fournit comme
observations `stableStructuralObservationSnapshot naming`, donc une
reconstruction du snapshot cible. L'analyse stocke à la fois l'assemblage
calculé et ces fragments reconstruits.

Dans [IncrementalChecker.lean](../../RelationalPerimeter/Agents/Neural/IncrementalChecker.lean),
vers la ligne 602, `buildIncrementalCheckedUpdate` appelle :

```lean
let certificate := assembleStateConstitution analysis.fragments
```

[StateConstitutiveCertificate.lean](../../RelationalPerimeter/Agents/Neural/StateConstitutiveCertificate.lean)
recopie les observations de ces fragments. Le code généré confirme ce chemin
de données. La preuve d'égalité avec l'assemblage transporté ne transforme
pas ce chemin en consommation de cet assemblage.

La fixture
[LearnedTargetPayloadCannotReplaceTransportedSource.lean.fail](../../Tests/ExpectedFailure/LearnedTargetPayloadCannotReplaceTransportedSource.lean.fail)
rejette une égalité entre listes différentes. Elle ne teste pas encore la
substitution effective au point de construction du certificat installé.

**Correction :** faire construire les données du certificat retourné depuis
les fragments source effectivement transportés et les fragments invalidés
recalculés. Le certificat installé doit consommer cet assemblage exact.
Conserver les équations nécessaires, mais ne pas les employer comme
substitut à cette consommation. Les compteurs doivent suivre ce chemin
réel, pas une sélection calculée en parallèle.

Obligations concernées : G8, RC2, RC5, S6. Traitement : L5–L7 et L11.

### F4 — Le recheck et l'incrémentalité ne ferment pas encore le domaine requis

Dans [ParameterizedCompiledCheckerFamily.lean](../../RelationalPerimeter/Agents/Neural/ParameterizedCompiledCheckerFamily.lean),
vers la ligne 717, `analyzeScalingIncrementalUpdate` commence par
`checkInitial scalingExecutableInterface update`, puis construit son
assemblage et sa décision de transition. La cible est donc entièrement
vérifiée avant le traitement présenté comme incrémental.

La correction des conditions locales est réelle : elles ne supposent plus
le succès global de cet analyseur. Il reste néanmoins un calcul complet
préalable, incompatible avec une revendication de revérification évitée.

Dans l'instance apprise, l'étape étendue possède un chemin de reconstruction
complète. L'équivalence nommée entre incrémental et complet sur les candidats
initiaux ne suffit pas à établir la même propriété pour les mises à jour
successives requises, indexées par leur agent courant.

**Correction :** conserver un recheck complet indépendant et fermer les
conditions autonomes, l'équivalence d'acceptation et la correspondance du
successeur sur le domaine successif annoncé. L'incrémental ne doit pas appeler
ce recheck pour produire d'abord un certificat cible complet. Décodage,
validation de format, calcul du graphe, revérification sémantique et assemblage
doivent être distingués.

Une transition dont tout le cône pertinent est affecté peut légitimement
nécessiter une revérification complète. Il faut une branche locale réellement
réutilisatrice et une branche étendue correctement recalculée, pas interdire
tout contrôle complet. La famille structurelle à obligations unitaires reste
un microbenchmark, pas le remplacement de la chaîne apprise substantielle.

Obligations concernées : G4, G7–G8, RC3, RC5, P6, P8. Traitement : L1–L2,
L5–L7 et L10.

### F5 — Le passage après oubli n'est pas une transition du runtime fermé

[LearnedFutureConstitutiveClosure.lean](../../RelationalPerimeter/Agents/Neural/LearnedFutureConstitutiveClosure.lean)
construit un oubli historique, une continuation permise et une absence de
permission de récupération. Les définitions `LearnedPostForgettingRequest`
et `LearnedPostForgettingPermission`, vers les lignes 308–320, restent
distinctes des transitions du méta-contrat appris.

Celui-ci prévoit `installAligned` et `installExtended`. La continuation
après oubli n'est pas consommée comme une `OperationalContractTransition`
par `submitUpdate`, avec installation de l'état réduit et ses obligations.
Le paquet conjoint stocke des résultats de lignée et d'oubli, mais ne produit
pas ce passage supplémentaire de l'API.

**Correction :** raccorder la réduction et le régime après oubli au
méta-contrat et au runtime existants. Pour une transition de contrat, transporter
les observations encore justifiées ou refuser la transition avant effet.
Ne pas reconstruire la provenance oubliée. Ne pas ajouter une seconde API
qui contournerait le checker et le certificat de l'état courant.

Il faut conserver les couches : les deux origines sont historiquement
distinctes avant oubli, alors que leur projection `futureSourceOfState`
peut déjà être égale. Cette égalité aval ne nie pas l'histoire source et ne
prouve pas à elle seule l'installation d'une réduction dans le runtime.
La fonction de réduction lit effectivement des données de runtime : le
défaut n'est pas une prétendue absence totale de connexion, mais l'absence
de la transition contrôlée et consommée requise.

Il n'est pas demandé d'accepter un contrat qui exigerait une information
irrécupérable. Le refus justifié de cette transition est le résultat correct.
La continuation positive autorisée et l'oubli non trivial doivent rester
construits.

Obligations concernées : G1, G5–G6, RC5–RC6, P4–P5. Traitement : schéma
dès L1, producteurs en L4, contrôle et installation en L5–L8.

### F6 — Une assertion de complexité n'est pas justifiée

Le commentaire d'`affectedWithin`, vers la ligne 756 de
[AffectedConstitutiveCone.lean](../../RelationalPerimeter/Agents/Neural/AffectedConstitutiveCone.lean),
qualifie le calcul de linéaire dans le graphe exploré grâce aux nœuds visités.
Or `constitutivePredecessors` parcourt la liste d'arêtes à chaque tour,
les recherches d'appartenance utilisent des listes et la récursion bornée
ne s'arrête pas explicitement sur une frontière vide.

**Correction :** retirer l'affirmation de linéarité non établie ou la remplacer
par une borne réellement justifiée pour l'algorithme utilisé. Une optimisation
éventuelle doit préserver le résultat et être mesurée. Aucune nouvelle
obligation de théorème asymptotique général n'est ajoutée à la cible : c'est
l'affirmation actuelle trop forte qui doit être corrigée.

Obligations concernées : C13, C15, S6. Traitement : L6 puis L10–L12.

### F7 — La comparaison confirmatoire et le gain pratique restent ouverts

La [campagne v6](../../experiments/constitutive-neural-alignment/v6/README.md)
reste historique, avec `confirmatory_results_present=false` et
`confirmatory_run_permitted=false`. Elle ne fournit pas la comparaison
confirmatoire exigée contre les six classes, la méthode relationnelle et
la combinaison de référence.

Les [résultats v8](../../experiments/constitutive-neural-alignment/v8/SCALING_ANALYSIS.md)
rapportent 35 traces et 210 mises à jour. À la taille 80, la médiane
incrémentale de la trace est de 70 777,626 ms contre 10,522 ms pour le recheck.
Le critère préenregistré de gain pratique est faux. Le contrôle d'archive
signale aussi `source_reconstructable=false` : sa réussite dans ce mode ne
reconstitue pas le snapshot source manquant.

**Correction :** préserver ces archives et résultats défavorables. Préparer
une nouvelle version reproductible, avec snapshot exact récupérable, puis
exécuter la comparaison sur la propriété complète pertinente. La nouvelle
campagne ne doit ni écraser v6/v8, ni déclarer qu'une archive est devenue une
validation du code corrigé. Un adaptateur absent laisse une obligation
ouverte, il ne constitue pas une victoire comparative.

Obligations concernées : G9–G10, C18, R1–R8, P1–P8, S1–S8.
Traitement : préenregistrement en L8 avant toute nouvelle production
confirmatoire, exécution en L9–L10, appréciation et audits en L12.

### F8 — Le texte, la matrice et le statut scientifique doivent être raccordés

Le [registre](../scientific-claims.json) contient désormais
`CONSTITUTIVE_NEURAL_ALIGNMENT_CLOSED_RUNTIME`, avec la révision d'évidence
`27fd39e23a04f7f25629c05cc8f2f1c19107cf2d`. Ses statuts restent :
`reader=pending`, `translation=pending`, `independent=not_recorded`.

Les introductions des textes
[français](../alignement-constitutif-neuronal-incremental.fr.md) et
[anglais](../incremental-constitutive-neural-alignment.en.md) parlent encore
d'un claim proposé et préparé avant son enregistrement. Cette présentation
est périmée. Les formulations sur le transport hors cône et la clôture
conjointe doivent, elles aussi, être confrontées à F1–F5.

**Correction :** rendre les états documentaires exacts, puis réexaminer la
[matrice d'implémentation](NEURAL_ALIGNMENT_IMPLEMENTATION_MATRIX.md), les
passages FR/EN et les quatre lectures de dépendance du registre après
réparation. Ne pas déclarer une revue indépendante acquise. Ne pas réduire
la cible terminale pour rendre le code actuel conforme. Une correction de
preuve ou de dépendance rouvre les revues concernées.

La [revue interne de 27fd39e](REVUE_CLAIM_PAR_CLAIM_27fd39e.fr.md) reste une
évidence historique de son propre examen, pas une certification indépendante
ni une réfutation automatique des constats présents.

Obligations concernées : C13–C18, S7–S8. Traitement : signalement dès L0,
lecture et réparation documentaire en L11–L12, sans rafraîchissement mécanique.

## 6. Tableau RC1–RC6 de cette révision

Les intitulés suivants renvoient à la définition normative unique de RC1–RC6.
« Présent » pour une sous-preuve ne ferme pas le raccord conjoint.

| Critère | État à 8a945f2 | Condition de clôture conservée | Étapes |
| --- | --- | --- | --- |
| RC1 — Origine déclarée | Distinctions reçues/produites explicites à préserver. | Paramètres, exigences, contextes, norme, admissions et schémas identifiés avant leurs conclusions ; pas d'autojustification normative. | L1, L8, L11–L12 |
| RC2 — Instanciation authentique | F1 et F2 bloquants ; F3 empêche la consommation annoncée. | Même run maître et mêmes occurrences jusqu'au certificat installé, sans reconstruction indépendante. | L2–L3, L5–L8, L11 |
| RC3 — Indépendance de la réalisation | Témoins du séparateur indépendants de la réalisation candidate ; ancienne circularité globale du checker de mesure corrigée. | Obligations autonomes, source non définie par la projection candidate ni par le succès du contrôle à caractériser ; certificats antérieurs et réflexion constructive légitimes. | L1, L4–L6, L10–L11 |
| RC4 — Conséquences générales | Raccord neuronal concret présent. | Préserver le contrat fixé et le théorème pour toute mémoire et toute réalisation exacte ; reconstruire les témoins sur les productions corrigées si elles changent. | L4, L7–L8, L11 |
| RC5 — Transport au fil des transformations | F1–F5 empêchent la clôture. | Transport réellement consommé à travers reconfiguration, décodeur, action, effet, successeur, mémoire et contrat ; revérification avant effet des obligations invalidées. | L1–L8, L11 |
| RC6 — Réalisations positives et prévention | Deux installations, réalisation exacte, oubli et refus existent ; leur raccord complet reste ouvert. | Réunir les transformations non identitaires, les adaptations successives, l'oubli et la continuation contrôlée, la réalisation exacte positive et le refus du contournement dans la même lignée et la même API. | L3–L4, L7–L9, L11 |

## 7. Ordre obligatoire des corrections

La numérotation L0–L12 conserve celle de l'audit précédent. Les acquis de la
section 3 ne sont pas à réécrire sans nécessité. Chaque lot ajoute
immédiatement ses tests positifs et négatifs ciblés. L11 ne reporte pas ces
contrôles à la fin.

Les dépendances essentielles sont : schémas et agent courant avant
décodeurs/checkers, production avant certification, assemblage consommé avant
installation, protocole gelé avant matériaux confirmatoires. Les interfaces
après oubli doivent être prévues en L1, pas ajoutées après coup comme une
API parallèle.

### L0 — Conserver le socle et figer l'inventaire des écarts

1. Préserver `8a945f2`, les audits antérieurs et les archives expérimentales.
   Inspecter le diff avant toute future écriture.
2. Conserver les gates réparées, la couverture des exécutables et les
   régressions positives de nommage, succession et RC4.
3. Consigner F1–F8 comme ouverts dans le suivi de correction. Une gate verte
   n'autorise pas à marquer G1–G10 ou RC1–RC6 conjointement clos.
4. Préserver les preuves Gödel/Tarski/HA et les interfaces génériques correctes.

Sortie : baseline reproductible et écarts attribués à leurs déclarations,
sans réécriture des verdicts historiques. Aucun nouveau commit n'est
implicitement autorisé par ce plan.

### L1 — Fixer les obligations autonomes et les transitions attendues

1. Cartographier contrat opérationnel, obligations `…At state`, méta-contrat
   et `futureContract`, avec formation, exécution, preuve et transport.
2. Définir les conditions de reconfiguration à partir du système source,
   de son run exact, de la nouvelle exigence, du contexte et de l'autorisation
   effectivement requis. Ne pas renommer des ports pour simuler C5/G3.
3. Fixer le schéma d'observation indépendamment de la réalisation candidate.
   Construire les témoins sources sans recevoir sa projection ou son exactitude.
4. Définir les transitions admissibles et leurs obligations après oubli :
   continuation permise, transport justifié vers le contrat cible ou refus.
5. Indexer les interfaces par l'agent courant et le contrat courant, pas
   seulement par le couple initial/aligné. Les décisions locales restent
   indépendantes du succès du checker complet à caractériser.

Sortie : spécification explicite de RC1/RC3 et des transitions requises.
Une modification nécessaire d'une instance rouvre ses preuves et revues,
sans modifier rétrospectivement les contrats historiques.

### L2 — Conserver la sérialisation complète et les identités exactes

1. Préserver la correction du nommage accepté, y compris le cas renommé.
2. Raccorder programme, encodage, poids, arêtes, ports, décodeur, autorisation,
   mémoire et contrat concernés au matériel réellement décodé.
3. Distinguer identité stable et position `Fin`. Fermer les correspondances
   de versions requises, avec insertions/suppressions/réindexations et
   invalidation des fragments non transportables.
4. Fournir aux checkers le décodage indexé par leur état source courant.
   Ne pas restaurer silencieusement un exemplaire canonique après acceptation.

Sortie : les données certifiées et installées sont celles reçues et décodées.
Tests : nommage admis conservé, correspondance invalide refusée, mauvais
état source et mauvaise version rejetés avant installation.

### L3 — Fermer la production causale et partager action, effet et successeur

1. Réutiliser les interfaces de `Reconfiguration.lean` pour fermer F1 sur
   l'artefact appris, sans nouvelle API parallèle ni certificat cible reçu.
2. Calculer les transformations locales non identitaires et leur composition,
   puis dériver la proposition depuis la même exécution.
3. Prouver les interventions des ressources prescrites du système antérieur,
   de la nouvelle exigence, du contexte et de l'autorisation incorporée.
   Ne pas retoucher les poids appris pour fabriquer ces preuves.
4. Produire une seule action. Faire consommer cette valeur exacte par le
   producteur d'effet, puis le même effet par événement, mémoire et successeur.
   Réparer les branches alignée et étendue.
5. Remplacer les deux régressions G3 mal attribuées et ajouter le contrôle
   de partage sur le code compilé du chemin appris.

Sortie : G2/G3 sont établis sur les producteurs concernés. Tests ciblés :
ressource source sans rôle, exigence contournée, autorisation non consommée,
action étrangère, effet reconstruit et successeur substitué. Une égalité de
valeurs ne doit pas masquer une substitution d'occurrence.

### L4 — Préserver RC4 et raccorder l'oubli au régime de continuation

1. Relier `futureSourceOfState` aux états exacts produits en L3.
2. Conserver les requêtes admises/refusées, l'égalité des lectures immédiates
   aligné/contournement et leur séparateur non vide. Ne pas affaiblir C10.
3. Préserver le théorème universel neuronal et sa réalisation exacte positive.
   Si ses sources changent, refaire le raccord de la preuve aux mêmes productions.
4. Exécuter la réduction depuis deux origines historiquement distinctes,
   encore renseignées avant l'action, et produire la mémoire réduite consommable.
   Conserver préservation de tous les futurs couverts et non-récupérabilité,
   sans confondre ces deux propriétés.
5. Produire les témoins de transition après oubli prévus en L1, pour le
   méta-contrat existant. Les obligations du contrat cible sont transportées
   seulement lorsqu'elles restent justifiées, sinon la transition est refusée.

Sortie : les producteurs des futurs et de la réduction sont raccordés. Leur
installation et leurs refus par `submitUpdate` restent à fermer en L5–L8.
Ne pas demander de fusionner la paire séparée sous le même contrat exact.
Les séparateurs vides restent légitimes ailleurs : seul le cas non trivial
déjà requis doit conserver son futur non vide.

### L5 — Fermer les checkers autonomes et le recheck indépendant

1. Consommer des entrées sérialisées sans certificat cible préfabriqué.
2. Construire les preuves depuis décodage, exécution et décisions locales
   réfléchies sur le domaine et la base causale finis déclarés.
3. Conserver la correction des conditions locales de la famille de mesure.
   Ne pas réintroduire une spécification identique au succès global du checker.
4. Construire un recheck complet indépendant des résultats et fragments de
   l'incrémental, indexé par l'agent courant, pour le domaine successif requis.
5. Fermer correction et complétude relative sur ces conditions autonomes,
   y compris pour les transitions de contrat et le régime après oubli.

Sortie : G7 est fermé dans les instances requises. La référence complète
ne reçoit pas le verdict incrémental comme oracle. Aucune décidabilité
universelle de propriétés sémantiques n'est ajoutée à la cible.

### L6 — Faire consommer la réutilisation et prouver l'équivalence

1. Construire le graphe causal hétérogène depuis les données exactes de
   réseau, décodeur, action, effet, successeur, mémoire et contrat.
2. Calculer le cône affecté et justifier les correspondances entre versions.
   Corriger le commentaire de complexité F6 sans annoncer de borne non prouvée.
3. Transporter les fragments hors cône depuis le certificat source réel,
   recalculer les fragments invalidés et construire les données finales
   du certificat **depuis cet assemblage**, sans snapshot cible régénéré.
4. Supprimer la certification complète préalable du chemin local revendiqué
   incrémental. Conserver les contrôles de décodage et de cohérence nécessaires
   et les comptabiliser séparément.
5. Démontrer équivalence d'acceptation et correspondance du successeur
   certifié avec L5 sur le même domaine et la même propriété.
6. Fermer un cas local avec transport non vide et un cas étendu légitimement
   recalculé. Étendre le raccord aux étapes successives requises, pas seulement
   à trois candidats du premier état.

Sortie : le certificat qui sera installé consomme les fragments transportés.
Tests : substitution au point réel d'assemblage, certificat d'une autre
version, égalité de valeur sans origine admissible, contrôle du code généré
et accord avec la référence indépendante. Les compteurs distinguent travail
transporté, recalculé et autres calculs nécessaires.

### L7 — Fermer l'installation, les traces et l'accessibilité après oubli

1. Utiliser l'API dépendante existante et les producteurs/checkers de L2–L6.
   La queue consomme exactement le `next` retourné par l'étape précédente.
2. Installer le certificat issu de l'assemblage consommé, avec la décision
   de transition réellement utilisée, y compris après réduction mémoire.
3. Fermer les transitions positives successives et la continuation autorisée
   après oubli. Réaliser aussi les refus de transitions non justifiées.
4. Prouver l'accessibilité certifiée des états installés et l'absence
   d'action effective ou de successeur installé en cas de refus. Les calculs
   de vérification et les simulations contrefactuelles restent purs.
5. Conserver les trois quantifications de la section 2 et leurs indices.

Sortie : G4/G5 et les transports RC5 sont raccordés aux installations.
Ne pas ajouter une borne de deux étapes au théorème générique. La présence
de deux étapes positives reste une non-vacuité requise, pas une preuve que
toute adaptation proposée serait admise.

### L8 — Geler les protocoles puis fermer l'instance apprise conjointe

Avant toute **nouvelle production confirmatoire**, figer dans une nouvelle
version les protocoles d'apprentissage/transformation et de comparaison :
provenance, droits de réemploi, graines, données ou règles de génération,
paramètres, commandes, versions d'adaptateurs, propriétés communes,
traductions, six classes, R1–R8, méthode relationnelle, combinaison de
référence, recheck et critères P1–P8/S1–S8. Les essais de développement restent
exploratoires. Les empreintes des entrées précèdent le run ; celles des
sorties sont enregistrées après production, sans sélection opportuniste.

1. Conserver l'indépendance de l'artefact appris. Calculer ses certificats
   depuis son décodage, sans choisir ses poids dans les preuves.
2. Réunir sur la même lignée les transformations non identitaires, plusieurs
   exigences et contextes, les rôles causaux prescrits, les reconfigurations
   successives, la réutilisation locale et l'oubli avec continuation contrôlée.
3. Construire depuis le même agent et la même intention admise
   `alignedUpdate` et `bypassUpdate`, égaux sur tout le domaine courant
   canonique. La même API accepte le premier et refuse le second pour la
   dépendance effectivement manquante, non pour son étiquette.
4. Relier la continuation non vide discriminante au contrat du runtime.
   Le candidat refusé reste une simulation pure, sans effet installé.
5. Refaire le paquet conjoint : chaque composant doit consommer les mêmes
   runs, occurrences, états, fragments et transitions, pas seulement stocker
   des théorèmes séparément vrais.

Sortie : RC1–RC6 et G1–G10 fermés ensemble sur l'instance apprise substantielle.
Les cas publics restent des régressions, pas des remplacements de membres
manquants de cette instance. Un changement de protocole après gel impose
une nouvelle version avant les nouvelles productions concernées.

### L9 — Exécuter la comparaison de capacité complète et équitable

1. Exécuter les six classes, la méthode relationnelle, la combinaison de
   référence et le recheck selon le protocole de L8.
2. Fournir aux méthodes les données pertinentes qu'elles savent exploiter :
   artefact, interventions, futurs et contrats. Ne pas réduire toutes les
   baselines à la table courante.
3. Vérifier les correspondances de propriétés, domaines, arithmétiques,
   versions et frontières de confiance. Compter les traductions requises.
4. Réaliser les raccords de la combinaison de référence sans lui donner
   notre verdict final ou notre certificat cible comme oracle.
5. Couvrir P1–P7, les ablations autorisées et les critères S1–S5/S7–S8.
   Relier chaque cellule à une preuve ou une sortie reproductible et conserver
   son statut exact, y compris les succès des méthodes concurrentes.

Sortie : gain résiduel expliqué face aux capacités réellement comparées.
Une absence d'adaptateur, une traduction non réalisée ou un verdict hors
interface ne vaut pas impossibilité générale. L'indiscernabilité par table
courante ne prouve ni acceptation nécessaire du contournement ni échec de
toute autre méthode.

### L10 — Mesurer l'échelle sur la propriété complète pertinente

1. Conserver v5, l'échec v7 et les résultats v8. Ne pas prétendre récupérer
   un snapshot absent par simple actualisation d'empreinte.
2. Figer un nouveau snapshot source autonome et récupérable avec protocole,
   tailles, répétitions, incertitude, limites, règles d'échec et seuils de gain.
3. Construire une famille dont graphes causaux pertinents, obligations et
   traces croissent, avec cônes locaux et étendus. Les obligations unitaires
   de la famille structurelle ne remplacent pas cet exercice substantiel.
4. Comparer le même checker compilé et la référence indépendante sur la
   même propriété et le même état source. Compter conversion, initialisation,
   construction, vérification, assemblage, installation, exécution et mémoire.
5. Publier tous les résultats, les coûts cumulés et amortis, les tailles de
   certificats/deltas et les fragments réellement transportés/recalculés.

Sortie : P8/S6 évalués dans leur vraie portée. La publication des coûts est
obligatoire. Une économie n'est établie que par le critère préenregistré
correspondant, jamais par un compteur de sélection. Un résultat défavorable
reste défavorable et ne réfute pas, à lui seul, un théorème formel.

### L11 — Réexaminer le candidat complet et toutes ses régressions

1. Refaire C1–C17, G1–G10 et RC1–RC6 par lecture des énoncés complets,
   producteurs, dépendances, transports et consommateurs.
2. Vérifier les fixtures sémantiques nouvelles, leurs diagnostics et sites.
   Les tests de présence d'un nom ne valent pas fermeture de son obligation.
3. Auditer toutes les déclarations concernées sans axiome interdit, avec
   un seul bloc `AXIOM_AUDIT` par fichier, et conserver la couverture des
   constantes écrites ainsi que l'union des exécutables.
4. Exécuter build, frontières d'import, stratification, code généré,
   fixtures, manifestes et contrôles documentaires disponibles. Les échecs
   d'évidence dus à des modifications doivent être signalés, pas masqués.
5. Vérifier les anciennes preuves et le diff, sans modifier Gödel/Tarski/HA
   pour faciliter l'instance neuronale. Relire la matrice et les textes FR/EN
   séparément, puis les confronter aux preuves.

Sortie : prévalidation complète du candidat. Les empreintes encore périmées
ne deviennent fraîches qu'après le gel et le raccord contrôlé de L12.
Tous les contrôles officiels restent requis avant la soumission extérieure.

### L12 — Livrer l'évidence scientifique et obtenir les deux audits requis

1. Corriger le statut documentaire F8 et les affirmations de consommation,
   de généralité et de coût selon les résultats effectivement obtenus.
   Ne pas abaisser la cible pour déclarer une clôture.
2. Après autorisation explicite, créer le commit d'évidence contenant sources,
   contrôles, textes et matériaux nécessaires. Raccorder le registre à cette
   révision existante après lecture des changements et réouverture des revues.
3. Faire passer sur le snapshot raccordé les autotests, `--static`, le build,
   `--lean`, les audits et les deux portails complets `verify.ps1`/`verify.sh`.
   Distinguer commit d'évidence et commit de registre effectivement examinés.
4. Préparer deux examens distincts : validité formelle et conceptuelle,
   puis portée comparative et nouveauté. Fournir les sources et textes complets,
   toolchain, dépendances, protocoles, résultats et identifiants exacts.
   L'accès distant ne doit pas être le seul moyen de lire les matériaux.
5. Soumettre seulement après autorisation et réussite des contrôles requis.
   Lire intégralement les rapports, vérifier leurs révisions et traiter leurs
   objections. Un verdict négatif ou inconclusif ne ferme pas la cible.
6. Enregistrer les évidences réellement obtenues, sans promettre le verdict.
   Toute correction affectant leur portée impose un nouveau gel et la reprise
   des contrôles/revues concernés.
7. Repasser les gates après finalisation. Avant une fusion autorisée, retirer
   les plans temporaires, conserver les rapports scientifiques nécessaires,
   vérifier liens, FR/EN, manifeste et diff, puis le commit fusionné.

Sortie : C18, les critères scientifiques et les audits requis sont réellement
fermés sur leurs révisions exactes. L'inscription d'une obligation dans ce
plan ne constitue pas son résultat.

## 8. Couverture intégrale à conserver pendant l'exécution du plan

### C1–C18 et G1–G10

| Obligations | Lots et contrôles principaux |
| --- | --- |
| C1, C6, G4 | L1–L2, L5–L8 : indexation par l'agent courant et quantification sur toute trace acceptée |
| C2–C5, C7, G2–G3 | L3, L8 : transformations et causalité des ressources exactes, autorisation incorporée |
| C8–C10, G6 | L4, L7–L8 : oubli, réduction non triviale, futurs exacts et passage après oubli |
| C11 | L3, L5–L8 : préservation dirigée proposition–action et consommation dans l'effet |
| C12, G9–G10 | L8–L9 : constructions positives substantielles, lignée apprise et contournement latent |
| C13, C15 | L1, L6, L11–L12 : vocabulaire, dépendances et portée scientifique exacte |
| C14, C16 | Tous les lots puis L11 : fixtures sémantiques et absence de régression |
| C17 | L11–L12 : validation Lean complète et audits des dépendances |
| C18 | L8–L12 : livraison, comparaisons et rapports indépendants effectivement obtenus |
| G1, G5 | L1, L4–L8 : transitions de contrats décidées, consommées, refus avant effectuation |
| G7–G8 | L2, L5–L7, L10 : décisions autonomes, recheck indépendant, transport consommé et coûts |

### Comparaisons et critères scientifiques

Le corpus **R1–R8 reste celui du rapport normatif lié en section 2**, avec ses
références primaires et ses passages à examiner. Il n'est pas remplacé par
une nouvelle recherche bibliographique dans cet audit de code. Les travaux
sur le code auto-modifiant certifié, les interventions causales neuronales,
l'assurance adaptative, la vérification neuronale incrémentale, le shielding,
les autorisations et les propriétés relationnelles restent tous à comparer
dans leur portée réelle.

| Épreuve | Preuve ou expérience attendue dans le plan |
| --- | --- |
| P1 — Contournement latent | L8–L9 : même source, intention et table courante, différence causale et futur non vide |
| P2 — Décodeur ou action modifié | L3, L6, L9 : cas admis et violation, invalidation et accord avec recheck |
| P3 — Contrat modifié | L1, L5–L7, L9 : admission consommée, transport justifié ou refus avant installation |
| P4 — Oubli et continuation | L4, L7–L9 : oubli positif exact, non-récupérabilité et variante perdant un futur requis |
| P5 — Contrat après oubli | L1, L4–L9 : transition réelle de l'API, aucune récupération fictive |
| P6 — Succession et fragments incohérents | L2, L6–L9 : rejet des mauvaises versions, occurrences et successeurs |
| P7 — Intégration et ablations | L9 : méthode relationnelle, combinaison de référence, garantie perdue localisée |
| P8 — Échelle et utilité | L10 : même propriété substantielle, graphes/traces croissants, coûts complets |

S1–S8 restent obligatoires : fidélité du corpus, comparabilité sémantique,
comparateurs substantiels, raccord nouveau identifié, séparation utile et
non-vacuité, réutilisation et coût, attribution et reproductibilité,
conclusion scientifique contrôlée. Les six classes de comparaison ne sont
remplacées ni par R1–R8 seuls, ni par la seule référence de recheck.

Les statuts `certified`, `observed`, `not-certified`, `out-of-interface` et
`adapter-unavailable` restent distincts. La disponibilité d'une preuve,
l'expressibilité d'une propriété et l'existence d'un chemin exécutable
fermant ses prémisses sont trois questions différentes.

Le gain de capacité conjointe doit subsister après examen des garanties
réelles des autres méthodes et de leurs combinaisons. Un gain de temps ne
le remplace pas. Une nouveauté comparative ne se déduit ni du nom du cadre,
ni du nombre de lemmes, ni d'un build réussi. Si le gain demandé n'est pas
établi, la cible correspondante reste ouverte : son critère n'est pas abaissé.

## 9. Critère final de clôture

La correction complète exige simultanément :

1. F1–F6 fermés par les constructions, consommateurs et régressions correspondants ;
2. toutes les lignes C1–C18, G1–G10 et RC1–RC6 rattachées à leurs énoncés,
   hypothèses, producteurs, transports et consommateurs sur la même évidence ;
3. réalisations positives conjointes et refus effectifs de la même API,
   sans collage de certificats issus de dispositifs indépendants ;
4. protocoles, comparaisons R/P/S et coûts réellement exécutés et examinés,
   sans falsification des résultats historiques ou avantage d'interface fabriqué ;
5. textes, registre et contrôles frais, puis les deux audits requis lus et
   clos sur leurs révisions exactes.

**À 8a945f2, cette conjonction n'est pas établie.** RC4 et les autres acquis
de la section 3 restent reconnus. La prochaine correction prioritaire est
la chaîne causale et exécutée de L1–L3, avec le schéma après oubli anticipé
en L1, puis la consommation réelle des certificats et leur installation.

## Annexe A — Sondes complémentaires reproductibles

Les déclarations suivantes ont été compilées via `lake env lean --stdin`
pendant l'audit, sans écriture de fichier Lean dans le dépôt. Leurs cinq
audits sont sans axiome. Elles isolent des propriétés du code actuel,
elles ne sont pas des corrections à intégrer comme preuves de conformité.

```lean
import RelationalPerimeter.Agents.Neural.LearnedFutureConstitutiveClosure
open ConstitutiveSearch ConstitutiveSearch.NeuralAgent
open ConstitutiveSearch.NativeMechanism
open ContinuationSignatures
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem audit_installed_fragments_recompute_target :
    learnedAlignedGenericIncrementalSuccess.checked.next.certificate.structuralObservations =
      stableStructuralObservationSnapshot learnedAlignedStableNaming := by rfl

def audit_alternative_prior_state : ReconfiguredExecutionState independentLearnedRequirementFamily :=
  { learnedInitialState with system := learnedDecodedExtendedArtifact.system }

theorem audit_prior_network_changed :
    serializeNativeSystem audit_alternative_prior_state.system ≠
      serializeNativeSystem learnedInitialState.system := by decide

def audit_alternative_transition : LearnedExecutedStateTransition
    LearnedContractTransitionPermission.installAligned
    audit_alternative_prior_state learnedAlignedState :=
  .executed audit_alternative_prior_state learnedAlignedInstallingAction rfl
    learnedAlignedInstallingEffect rfl

theorem audit_forgetting_reduction_ignores_effect_memory
    (first second : LearnedEffectWitness learnedAlignedState) :
    independentLearnedFutureProjection
      (LearnedAlignedOperationalContract.futureSourceOfState first.targetState) =
    independentLearnedFutureProjection
      (LearnedAlignedOperationalContract.futureSourceOfState second.targetState) := by rfl

theorem audit_reduced_sources_equal_before_forgetting :
    LearnedAlignedOperationalContract.futureSourceOfState
        LearnedHistoricalStableOrigin.aligned.runtime.current.state =
      LearnedAlignedOperationalContract.futureSourceOfState
        LearnedHistoricalStableOrigin.renamed.runtime.current.state := by rfl

#print axioms audit_installed_fragments_recompute_target
#print axioms audit_prior_network_changed
#print axioms audit_alternative_transition
#print axioms audit_forgetting_reduction_ignores_effect_memory
#print axioms audit_reduced_sources_equal_before_forgetting
```

Interprétation limitée aux résultats obtenus :

- la première égalité ne prouve pas seule l'absence de réutilisation exécutée :
  F3 repose aussi sur les corps des producteurs et le code généré ;
- la transition alternative n'est pas une mise à jour démontrée acceptée
  par l'API fermée ;
- les deux dernières égalités concernent la projection future, pas l'identité
  des origines ni la fausseté des théorèmes d'oubli existants.

L'évaluation complémentaire suivante, avec les mêmes imports, a retourné
`[1100, 1101, 1102]` dans les deux cas :

```lean
#eval learnedRenamedSerializedUpdate.targetStableNaming.inputKeys
#eval match checkGenericIncrementalUpdate learnedIncrementalCheckerEngine learnedRenamedSerializedUpdate with
  | .error _ => ([] : List Nat)
  | .ok success => List.filterMap
      (fun (entry : StableNodeKey × StableArtifactObservation) =>
        match entry.1 with
        | .receivedInput serial => some serial
        | _ => none)
      success.checked.next.certificate.structuralObservations
```

## Annexe B — Commandes de contrôle pour la future livraison

À exécuter sur le snapshot corrigé avec sa toolchain épinglée et ses évidences
raccordées, sans interpréter leur succès comme un verdict scientifique :

```text
git rev-parse HEAD
git status --short
python3 scripts/check-scientific-docs.py --self-test
python3 scripts/check-scientific-docs.py --static
lake build
python3 scripts/check-scientific-docs.py --lean
pwsh -NoProfile -File scripts/verify.ps1
bash scripts/verify.sh
git diff --check
```

Les nouveaux contrôles de consommation et de partage appris doivent être
intégrés aux gates, pas exécutés comme sondes oubliées hors livraison.
Les journaux futurs identifieront la révision, l'environnement, les commandes,
les sorties, leurs codes de retour et les contrôles non exécutés éventuels.

## Annexe C — Vérification de la rédaction du présent rapport

Après rédaction, relecture intégrale du rapport et confrontation de l'ordre
L0–L12 aux critères normatifs, notamment RC1–RC6. Les acquis et les écarts
sont distingués, les clôtures locales ne remplacent pas la réalisation
conjointe et les exigences comparatives restent obligatoires.

Contrôles documentaires exécutés :

- `check-scientific-docs.py --self-test` : 7/7 ;
- `check-scientific-docs.py --static` : réussi, 24 affirmations et
  262 déclarations, revues ouvertes toujours signalées ;
- contrôle direct des 21 liens locaux du nouveau fichier : réussi ;
- contrôle d'espacement et inspection du statut Git : aucun changement
  de source, de registre ou de document normatif, seul ce Markdown est ajouté.

Aucune nouvelle compilation Lean, expérience, opération de commit/push ou
soumission d'audit extérieur n'a été effectuée pour cette rédaction.
