# Preuves et contrats de la chaîne constitutive et de la machine

Ce complément permet de vérifier le [texte français](TEXTE_CHAINE_CONSTITUTIVE_A_AUDITER.fr.md)
et sa [version anglaise](TEXTE_CHAINE_CONSTITUTIVE_A_AUDITER.en.md).
Il distingue les passages construits, leurs domaines et les contrôles
d'implémentation. Les noms abrégés ci-dessous sont toujours rattachés à leur
module par un lien ; ils ne désignent pas des copies des objets de production.

Cette revue locale porte sur les passages cités. Elle n'est ni un nouveau
verdict indépendant ni une lecture exhaustive de chaque ligne du dépôt.
La cible canonique et les contrats ne sont pas modifiés.

## Vérifications locales du 7 octobre 2026

Branche : `codex/integrated-master-machine-audit-20261006`.
Tête conservée : `39a3a352082e63c0fca27171d903bb367467b22c`.
L'arbre contient les ajouts locaux déjà présents au démarrage ; cette tête
seule n'est donc pas un identifiant du paquet étudié. Le contrôle d'empreintes
porte sur l'arbre local, avant et après cette rédaction.

| Vérification réellement exécutée | Résultat |
| --- | --- |
| `lake build`, toolchain `leanprover/lean4:v4.33.1` | Succès, 246 jobs, sans avertissement Lean ; build local avec réutilisation des sorties existantes. |
| `pwsh -NoProfile -File scripts/verify.ps1` | Succès sur Windows, 244 fichiers Lean, 23 fixtures de rejet. |
| `bash scripts/verify.sh` | Succès sur le même arbre local, mêmes 244 fichiers et 23 fixtures. |
| Audit exhaustif des constantes inclus dans les gates | 20 649 constantes, 243 modules, 364 exceptions générées, zéro exception écrite à la main. |
| Documentation scientifique incluse dans les gates | 17 entrées ; 59 déclarations publiques et 10 déclarations de tests résolues par Lean. Les revues ouvertes restent ouvertes. |
| Clients de cette revue, compilés hors du dépôt | Exemple à deux reprises reproduit ; 59 noms distincts audités, sans axiome. |
| Contrôles compilés inclus dans les gates | Chaîne de données, transitions appariées, origines des effets et rejet de l'écrasement d'événement par helper vérifiés aux frontières annoncées. |

La concordance FR/EN est une relecture locale des huit sections : mêmes
sources, mêmes quantifications, même domaine cohérent de minimalité, mêmes
contrats, même table de calcul et mêmes bornes de portée. Elle ne remplit pas
automatiquement les revues de traduction du registre.

Ces commandes n'ont pas été lancées dans un clone propre figé à un nouveau
commit. Les noms audités et les résultats calculés confirment les références
du texte ; ils ne remplacent pas l'examen sémantique des preuves ni un audit
indépendant. Le checker documentaire existant contrôle ses ancrages enregistrés,
pas à lui seul les affirmations de ce nouveau document de travail.

## Ce qui est fourni et ce qui est produit

| Donnée | Origine | Usage effectif |
| --- | --- | --- |
| Relations, témoins, générateur constitutif et origine publique | Fondation et construction de la famille | Constitution des occurrences, des histoires et de l'origine du maître. |
| État et préfixe reçus par une étape | Origine, puis production de l'étape précédente | Extraction, filtrage de provenance, découverte, application et formation de la tête. |
| Relation locale du maître | Recherche exécutée sur ce matériau | Action et autorisation de la décomposition ; composition des sorties. |
| Formule SAT, contextes admissibles et permission de lecture de la machine | Entrées reçues à l'interface du même maître | Ouverture, recherche dirigée, action sur les paquets, admission et lectures. |
| Sélecteur vivant retourné | Recherche vivante exécutée | Argument de l'ouverture SAT. Sa valeur est reconstructible depuis la profondeur dans cette famille. |
| Code SAT, frontière retenue et circuit | Normalisation après ouverture des contextes reçus | Routage ultérieur et entrée de la recherche SAT suivante. |
| Contrat et demandes futures | Spécification reçue avant la réduction de mémoire | Détermination des comportements à préserver. Le contrat n'est pas choisi après observation du regroupement. |

Le calcul ne reçoit pas une partition ni une largeur à réaliser. Les entrées
SAT sont néanmoins fournies : le texte ne dit pas que le maître public les
a engendrées. « Produit » désigne une provenance et une dépendance exécutée,
pas une imprévisibilité ou une nouveauté informationnelle.

## Passages entre les strates

### C01 Constitution et profils

Sources : [ConstitutiveGeneration](../../RelationalPerimeter/Computation/ConstitutiveGeneration.lean),
[RelationalProfileConstitution](../../RelationalPerimeter/Computation/ConstitutiveSearch/RelationalProfileConstitution.lean),
[RoleIndexedProfiles](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/RoleIndexedProfiles.lean),
[UnifiedPublicCertificate](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean).

- Formation : les histoires sont dépendantes ; la suite commence à l'état
  produit par la tête. Les identités constituées ont une réalisation et les
  accords positifs de source, formation, cible et provenance.
- Exécution : la génération fournit le matériau structural ; le maître en
  produit une histoire de rôles. Le carrier des profils est ensuite dérivé
  de cette histoire, non reçu comme une table booléenne globale indépendante.
- Preuve : les lois de retour de `positionOccurrenceTransport` et les accords
  de réalisation relient positions et occurrences. `class_carrier_exact` et
  `class_iff_on_executed_regime` raccordent directement la famille publique
  au carrier exécuté.
- Distinctions : positions, occurrences, profils, obligations et lectures
  quantitatives sont des objets de strates différentes.

À la classe générale, les relations peuvent être triviales. Le théorème fini
de largeur ne prouve pas leur non-trivialité et ne tire pas son contenu
combinatoire de leurs valeurs. La construction relationnelle non triviale,
la recherche et l'action sont celles du maître et de ses consommateurs cités.

### C02 Recherche et production locale avant la suite

Sources : [MasterResourceExecution](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/MasterResourceExecution.lean)
et [CausalOperationalExecution](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/CausalOperationalExecution.lean).

- Formation : `Cursor` contient des références typées vers l'état, le préfixe
  et leur accord de fraîcheur. La tête ne reçoit pas de queue future.
- Exécution : `discover`, `applyStage`, `decompose` et `assemble` lisent leurs
  références. `executeWithReferences` forme la tête avant son appel récursif
  depuis `continueWithReferences`.
- Preuve : `head_exact`, `cursor_head_exact`, `execute_succ`,
  `cursor_next_state` et `cursor_next_context` épinglent les raccords.
  `executeCausalOperationalExecutionHistory_head_independent` et
  `executeCausalOperationalExecutionHistory_allHeadsExact` portent sur les
  productions et leur indépendance envers l'horizon futur.
- Distinctions : un état reçu et son préfixe ne sont pas remplacés par une
  histoire achevée utilisée après coup. Cette temporalité est typée et
  exécutable ; ce n'est pas un chronométrage physique.

### C03 Sorties produites et obligations globales

Sources : [ExecutedOutputObligations](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ExecutedOutputObligations.lean)
et [UnifiedPublicCertificate](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean).

- Formation : les sorties locales enregistrées dans la décomposition
  stagewise composent la politique sur l'histoire des rôles.
- Exécution : `ExecutedOutput.ofStagewise` lit ces images ; `carry` porte
  chaque profil vers son résultat produit.
- Preuve : `ExecutedOutput.carry_action`, `Instance.carry_fibres` et
  `Instance.coDetermination_fibres` relient l'action, les cibles et leurs
  codéterminations. `value_reify` et `reify_value` sont les lois de retour
  entre les représentations d'obligations. La convergence des décisions
  exécutées permet ensuite de déduire `Instance.executed_width`.
- Distinctions : égalité de sorties n'est pas égalité de profils ; les lois
  de retour sur les obligations ne sont pas un inverse sur les sources.

`Instance.returned_action_exact` porte séparément sur l'action des
continuations acceptées. La convergence des sorties canoniques n'est pas
utilisée comme substitut à cette préservation.

### C04 Recherche vivante et recherche SAT

Sources : [ConstitutiveDiscovery](../../RelationalPerimeter/Computation/Machine/ConstitutiveDiscovery.lean),
[ConstitutiveLiveExecution](../../RelationalPerimeter/Computation/Machine/ConstitutiveLiveExecution.lean),
[MasterRuntime](../../RelationalPerimeter/Computation/Machine/MasterRuntime.lean).

- Formation : `fromMaster` reçoit le point de reprise du maître existant,
  la formule, les contextes et le scope. Une réception n'est pas une preuve
  d'atteignabilité de ces contextes depuis la course canonique.
- Exécution : `ConstitutiveExecution.produce` effectue la découverte vivante,
  la validation et l'application. `MasterMachine.advance` partage cette
  production et donne `production.action.selected` à `produceProblem`.
- Preuve : `produce_exact`, `advance_core_exact` et
  `advance_frontier_is_produced` relient ces constructions à leurs sorties.
- Distinctions : la valeur canonique du sélecteur peut dépendre seulement de
  la profondeur ; la décomposition SAT dépend aussi des contextes réellement
  reçus et peut différer à sélecteur fixé.

### C05 Relation SAT code et préservation

Sources : [AcceptedFrontierNormalization](../../RelationalPerimeter/Computation/ConstitutiveSearch/AcceptedFrontierNormalization.lean)
et [MasterRuntime](../../RelationalPerimeter/Computation/Machine/MasterRuntime.lean).

- Formation : le code de réduction est indexé par sa frontière source et sa
  frontière retenue. Une absorption contient le transport trouvé.
- Exécution : la normalisation effectue les recherches dirigées et construit
  ses branches de code selon leurs résultats. `produceProblem` réemploie
  ce code et sa frontière retenue.
- Preuve : `AcceptedIrreducibleFrontierReduction.preservation` évalue le
  code ; `ScopedProblemProduction.preservation` compose cette garantie avec
  celle de l'ouverture. `advance_preserves_SAT` expose la viabilité avant
  et après la reprise.
- Distinctions : les sources restent distinctes ; conserver la possibilité
  d'une continuation acceptée ne les identifie pas. `none` signifie qu'aucun
  transport n'a été fourni par ce chercheur, non qu'aucun transport n'existe.

### C06 Action configurée sur une nouvelle entrée

Sources : [FrontierCircuit](../../RelationalPerimeter/Computation/Machine/FrontierCircuit.lean)
et [MasterRuntime](../../RelationalPerimeter/Computation/Machine/MasterRuntime.lean).

- Formation : `ScopedProblemProduction` épingle le circuit à `lowerFrontier`
  du code découvert. Le paquet contient un slot et les bits du scope.
- Exécution : `FrontierCircuit.fire` utilise ce programme configuré ;
  `Routing.apply` vérifie la position puis applique le circuit.
- Preuve : `lowerFrontier_exact`, `ScopedProblemProduction.circuit_exact`
  et `route_exact` portent sur toute continuation typée de la frontière
  ouverte. `circuit_preserves_SAT` consomme en plus l'acceptation SAT de
  cette continuation et préserve SAT après transport.
- Distinctions : admission de position et taille n'est pas satisfiabilité.
  Une permutation de slots n'identifie pas les occurrences sources.

### C07 Sortie et recherche suivante

Source : [MasterRuntime](../../RelationalPerimeter/Computation/Machine/MasterRuntime.lean).

- Formation : `ScopedProblemProduction.next` contient la frontière retenue,
  le routage configuré et l'absence de résultat de paquet encore routé.
- Exécution : `advance` installe cette mémoire et le successeur de sa production
  vivante. À la demande suivante, il lit cette nouvelle frontière.
- Preuve : `advance_frontier_is_produced` est universel sur la mémoire reçue.
  Le client ci-dessous vérifie définitionnellement le consommateur de la
  seconde reprise ; la préservation se compose sur deux reprises.
- Distinctions : le raccord vivant vers SAT puis SAT vers la recherche SAT
  suivante est construit. Une rétroaction de SAT sur le moteur vivant n'est
  pas revendiquée.

### C08 Futurs et mémoire nécessaire

Sources : [ReducedLiveContract](../../RelationalPerimeter/Computation/Machine/ReducedLiveContract.lean),
[ReducedLiveMinimality](../../RelationalPerimeter/Computation/Machine/ReducedLiveMinimality.lean),
[ConstitutiveLiveExecution](../../RelationalPerimeter/Computation/Machine/ConstitutiveLiveExecution.lean)
et [MasterContract](../../RelationalPerimeter/Computation/Machine/MasterContract.lean).

- Formation : le scope et le contrat sont fixés avant la comparaison. Le
  runtime réduit contient le front vivant, ses valeurs autorisées, les
  connexions et la banque normalisée ; la machine intégrée ajoute sa mémoire SAT.
- Exécution : `projectMemory` extrait les valeurs finies autorisées ; le
  chemin réduit poursuit sans restaurer l'affectation fonctionnelle complète.
- Preuve : `ConstitutiveExecution.all_sources_exact` vaut pour tous les états
  sources et toutes les suites finies du noyau. `minimality` caractérise
  exactement l'égalité de projection par l'égalité des futurs sur les états
  cohérents ; `any_realization` impose cette distinguabilité à toute autre
  réalisation exacte. `MasterMachine.all_futures_exact` ferme séparément le
  contrat intégré.
- Distinctions : oubli sous le contrat n'est pas identification des sources.
  Minimalité du noyau cohérent n'est ni minimalité SAT complète, ni minimum
  d'octets, ni gratuité de l'interprète.

La cohérence de [MemoryInvariant](../../RelationalPerimeter/Computation/Machine/MemoryInvariant.lean)
est l'accord des longueurs des gates et des deux lectures de banque avec le
scope. La nécessité des connexions est reconstruite depuis une impulsion
admise de zéros par `futures_determine_connections` dans
[CausalDistinctions](../../RelationalPerimeter/Computation/Machine/CausalDistinctions.lean).
`future_determines_live_values` retrouve les valeurs depuis l'effet d'une
reprise, en utilisant cette connaissance des gates et leur involutivité.
Les connexions n'ont pas été ajoutées artificiellement à l'observation.

### C09 Partage des productions et effets

Sources : [MasterContract](../../RelationalPerimeter/Computation/Machine/MasterContract.lean)
et [check-integrated-machine-codegen.py](../../scripts/check-integrated-machine-codegen.py).

- Formation : le runner actif et la spécification à callbacks sont distincts.
- Exécution : `perform` retourne ensemble l'événement et le successeur ;
  `run` réemploie la même paire avant de parcourir la queue des demandes.
- Preuve : `run_shared_transition` fixe ce chemin et `run_exact` l'accorde à
  la spécification. Les contrôles compilés suivent aussi les origines de
  champs et effets entre helpers, pas seulement leurs noms.
- Distinctions : ces contrôles portent sur les chemins locaux supportés ;
  ils ne certifient pas tout le tas, les callbacks arbitraires d'un client,
  une architecture matérielle ou le coût total.

### C10 Largeurs après constitution et action

Sources : [UnifiedPublicCertificate](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/UnifiedPublicCertificate.lean),
[RolePolicySpectrum](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/RolePolicySpectrum.lean)
et [PublicRolePolicySpectrum](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/PublicRolePolicySpectrum.lean).

- Formation : les régimes sont surjectifs sur le carrier constitué. La
  politique comparative reçoit les rôles et leurs transports autorisés.
- Exécution : la lecture extensive énumère les profils ; l'image exécutée
  lit leurs sorties. La comparaison `pending` conserve certains rôles,
  sans prétendre découvrir à nouveau ces statuts.
- Preuve : `class_iff_on_master_carrier` et `class_iff_on_executed_regime`
  appliquent l'équivalence de pleine largeur au même carrier. `PolicySpectrum.width`,
  `injective_iff` et `spectrum` donnent les largeurs `2^k` des politiques
  concernées. `half_width` exhibe une politique non injective de largeur
  `2^(n-1)` pour tout nombre positif de rôles.
- Distinctions : seule la pleine largeur `2^n` est caractérisée par
  l'injectivité ; non-injectivité n'implique pas absence de toute croissance
  exponentielle. Aucune largeur ne constitue une borne de coût total.

## Carte des contrats

| Domaine | Demandes et résultats conservés | Garantie et restriction |
| --- | --- | --- |
| Profils du maître et sortie normalisée | Lectures de rôles et reprises de préfixe définies par [ProducedProfileContinuation](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ProducedProfileContinuation.lean) | Exactitude des événements et admissions du contrat ; l'irrécupérabilité du profil n'est pas un oubli universel de tout passé. |
| Noyau machine | Listes finies arbitraires de `advance`, `sample`, `pulse` ; observations, événements, admissions et refus | Exactitude sur tous les états sources. Minimalité et nécessité pour toute réalisation exacte sur les états cohérents, à scope fixé. |
| Machine intégrée | Demandes du noyau, `route`, `sampleProblem`, avec tous leurs entrelacements | `MasterMachine.all_futures_exact` ; pas de théorème de minimalité complète de la mémoire SAT. |
| Variable après action | Lectures répétées de la variable 10 dans [VariableMasterFutures](../../RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/VariableMasterFutures.lean) | `exact_future_fibres` et `every_exact_realization_distinguishes` ; ni impulsion ni reprise ni lecture arbitraire de l'histoire. |
| Consommateurs agents | `advance`, `inspect`, `obtain`, `propose` du contrat d'agent déjà construit | Signatures exactes sur les états atteignables, à maître et exigence fixés ; les [signatures](../signatures-de-continuation.fr.md) ne remplacent pas le moteur ou les droits de l'agent. |

La composition noyau vers machine intégrée est une réalisation exacte du
contrat combiné. Elle ne transporte pas automatiquement la minimalité du
noyau à ce nouveau domaine. Les témoins de lecture de la variable 10 et de
l'agent restent des consommateurs situés, non des étapes du scénario SAT.

## Exemple et reproduction locale

Le scénario utilise uniquement les objets du test
[MasterIntegration](../../Tests/Machine/MasterIntegration.lean).
`initialization_is_existing_master`, `same_live`, `same_depth` et `selector`
fixent le maître et les paramètres communs. `every_child_viable` construit
les continuations acceptées ; `source_distinct` sépare les sources.
`grouped_width`, `unresolved_width`, `same_finder_fails_both_ways` et les deux
preuves de paquet exposent la découverte et ses effets réels.

Ce client est compilable hors du dépôt par `lake env lean` après le build.
Il calcule la table du texte, sans fournir une décomposition attendue et
sans redéfinir un objet de production :

```lean
import RelationalPerimeter
import Tests.Machine.MasterIntegration
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ChainPresentationChecks
open ConstitutiveSearch SAT ConnectedFabric
open ReconfigurableMachine.LiveReduction

theorem next_search_receives_produced {scope : Scope} {formula : Cnf}
    (memory : MasterMachine.Memory scope formula) :
    MasterMachine.produceProblem scope formula
        (ConstitutiveExecution.produce (MasterMachine.advance memory).core.live).action.selected
        (MasterMachine.advance memory).problem.frontier =
      MasterMachine.produceProblem scope formula
        (ConstitutiveExecution.produce (MasterMachine.advance memory).core.live).action.selected
        (MasterMachine.produceProblem scope formula
          (ConstitutiveExecution.produce memory.core.live).action.selected
          memory.problem.frontier).reduction.retained := by
  rfl

theorem two_advances_preserve_sat {scope : Scope} {formula : Cnf}
    (memory : MasterMachine.Memory scope formula) :
    FrontierViable (generatedStructuralBranchSystem formula) memory.problem.frontier ↔
      FrontierViable (generatedStructuralBranchSystem formula)
        (MasterMachine.advance (MasterMachine.advance memory)).problem.frontier :=
  (MasterMachine.advance_preserves_SAT memory).trans
    (MasterMachine.advance_preserves_SAT (MasterMachine.advance memory))

#eval [false, true].map fun previous =>
  let first := MasterMachine.advance (MasterMachine.Checks.received previous)
  let second := MasterMachine.advance first
  (previous, first.problem.frontier.length,
    (ConstitutiveExecution.produce first.core.live).action.selected,
    second.problem.frontier.length)

#eval [false, true].map fun previous =>
  ((MasterMachine.perform (MasterMachine.advance (MasterMachine.Checks.received previous))
    (.route 0 [false])).1).problem.routed

end ChainPresentationChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms ChainPresentationChecks.next_search_receives_produced
#print axioms ChainPresentationChecks.two_advances_preserve_sat
/- AXIOM_AUDIT_END -/
```

Résultats obtenus sur l'arbre local étudié :

```text
[(false, 2, 14, 2), (true, 1, 14, 1)]
[some (1, [false]), some (0, [true])]
```

Les deux preuves ne dépendent d'aucun axiome. Il s'agit d'un contrôle
sémantique et d'un exemple évalué, non d'une campagne de coût confirmatoire.
Le raccord universel appartient déjà à `advance_frontier_is_produced` ; le
client vérifie son usage dans la deuxième recherche, pas une hypothèse ajoutée.

Le témoin [ValidAssignmentForgetting](../../Tests/Machine/ValidAssignmentForgetting.lean)
est distinct. `outside_permission_all_futures` démontre l'accord de tous les
futurs à scope 2 ; `separating_future` exhibe une reprise qui distingue à
scope 1. Ce sont des états reçus valides du noyau, pas deux nouvelles courses
SAT ni des préfixes déclarés publiquement atteignables.

## Registre revue et préparation de l'audit

Le [registre existant](../scientific-claims.json) couvre notamment
`MASTER_COUPLING`, `CONFIGURED_ACTION`, `FULL_FUTURES`, `MACHINE_EXAMPLE`,
`SINGLE_EXECUTION`, `ASSIGNMENT_FORGETTING`, `PROFILE_FORGETTING`,
`RESTRICTED_FUTURES`, `REACHABLE_SIGNATURE` et `PARTIAL_WIDTHS`.
L'entrée `CORE_MINIMALITY` référence explicitement
`ConstitutiveExecution.minimality` et `any_realization`, avec leur domaine
cohérent. Les ancrages français et anglais relient les sections du texte
aux affirmations correspondantes. La révision d'évidence est
`a13c9a707afb43f0dca79576d6bc073e1bcc1bfa`, qui contient ces textes et
leurs sources. Les revues concernées sont rouvertes ; aucun verdict
historique n'est reporté sur ce nouveau paquet.
Les statuts `pending` et `not_recorded` restent ouverts ; un contrôle statique
réussi ne constitue pas un avis scientifique indépendant sur ce texte.

Le nouveau protocole cite sans changement la cible canonique et S1–S8 /
G1–G10, puis demande l'examen du texte entier, de C01–C10 et de leurs
consommateurs. Il est épinglé séparément au paquet complet publié.
Le reçu de soumission est distinct de cette table : une acceptation API
ne constitue pas un verdict scientifique.
