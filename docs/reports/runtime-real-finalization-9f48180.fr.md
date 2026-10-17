# Rapport final de migration du runtime relationnel et des réels effectifs

## Révision examinée et statut

Révision d'évidence : `9f48180aa8c2aad43d2bc1cbee7419095d4b43dd`.

Ce rapport décrit la migration locale des anciens modules de réels vers la
chaîne constitutive active, la correspondance runtime–Cauchy effectif et leur
raccord au périmètre de Gödel. Il ne constitue ni une revue indépendante, ni
un verdict d'originalité. Les statuts enregistrés pour les deux affirmations
concernées restent `reader=pending`, `translation=pending` et
`independent=not_recorded`.

## Résultat de la migration

Les huit anciennes voies parallèles ont été retirées. La surface active est
désormais organisée par :

- `ConstitutiveRuntime`, pour la chaîne réception–recherche–action–préservation–
  autorisation–décomposition–continuation–mémoire ;
- `ProducedCompleteness`, pour les sources, limites, chaînes chronologiques,
  consommations exactes et normalisations historiques ;
- `AuthoritativeRuntime`, pour l'archive riche, les pas possédés, les cibles
  installées et la production du réel relationnel ;
- `CommonRealRuntime`, pour un runtime commun dont l'environnement exécutable
  est une donnée et dont la mémoire vivante est directement exécutée ;
- `RuntimeCorrespondence` et `EffectiveCauchyReal`, pour la correspondance
  numérique et le carrier externe sans quotient ;
- `GodelRealCorrespondence`, puis l'instance HA, pour fixer le même périmètre
  et la même base `H1` sans dériver les approximations de la contradiction.

L'inventaire de non-perte a comparé 397 déclarations historiques : 397 noms
ont été classés une seule fois, sans manque, ajout ni doublon. Les 29 éléments
classés comme anciennes surfaces publiques abandonnées ne portaient aucune
garantie indispensable sans remplacement. Les garanties retenues ont été
reliées à 329 contreparties formelles sans axiome ; 141 ont été restaurées à
l'identique et les dépendances anciennes ont été séparées des dépendances de
remplacement.

## Point causal critique du regroupement

Une version intermédiaire recréait une charge initiale à chaque ajout et ne
consommait donc pas effectivement la ressource historique transportée. Cette
voie n'appartient pas à la révision d'évidence.

Dans la révision examinée, `HistoricalSeed` fournit la charge normalisée du
préfixe. `advanceBatch` construit sa charge `transported` depuis cette ressource
complète, et `normalizeFresh` consomme seulement l'obligation fraîche sur ce
transport. Le type `BatchAdvance` retient `transportedExact` et
`resultFromTransport`; les théorèmes `consumed_exact` et `oldCharge_exact`
conservent le préfixe, les anciennes charges et leurs témoins. La cible de
`BatchGrouping.program` est produite depuis cette normalisation, installée par
`GroupingStep.next`, puis relue par `continueInstalled` depuis la ressource
`OwnedTarget` retenue.

Les tests positifs `lastHistoricalInputOwnsPrefix`,
`lastNormalizationConsumesTransportedResource`,
`lastNormalizationKeepsTransportedNear` et
`historicalResourceCannotBeFreshSeed` contrôlent cette chaîne. La fixture
`FreshSeedCannotReplaceTransportedBatch.lean.fail` rejette la substitution
d'une graine fraîche au site typé attendu.

## Mémoire runtime et portée de la minimalité

`CommonRealRuntime.Runtime` contient l'environnement — producteur et module —
et la mémoire vivante. `performReal` lit ces données dans l'état même.
`fixedEnvironmentMinimality` caractérise exactement la mémoire seulement pour
un environnement fixé. `archiveRealization` couvre les sources brutes, limites,
lots, continuations, lectures et refus de l'archive riche ;
`archiveMemoryMinimality` caractérise sa projection pour une famille fixée.

Ces résultats ne permettent pas d'oublier le producteur pour comparer deux
programmes différents. `NumericalFutureEquivalent` compare séparément leurs
readouts limites exécutés et n'identifie ni environnements, ni ressources, ni
occurrences. Les fixtures `MemoryCannotHideExecutableEnvironment`,
`MemoryEqualityCannotCompareEnvironments` et
`NumericalFuturesCannotIdentifyOccurrences` protègent ces restrictions.

## Correspondance et limites scientifiques

La présentation numérique d'un runtime provient de ses pas limites canoniques.
La construction inverse reçoit une présentation dyadique effective et forme une
famille exécutable. Les allers-retours sont exacts ou positivement équivalents
au niveau déclaré des readouts, des futurs limites finis et du carrier de
Cauchy effectif. Ils ne reconstruisent pas l'histoire riche depuis les valeurs.

Le résultat ne couvre pas tous les réels classiques. Il n'établit pas encore
les opérations de corps, l'ordre ou l'apartness, la densité, la propriété
archimédienne, la complétude d'ordre, `AC` ou `CH`. Le raccord Gödel fixe le
périmètre et rejette la fermeture totale du même régime ; il ne produit aucune
approximation numérique.

## Vérifications exécutées

Sur l'arbre qui a produit la révision d'évidence :

- auto-test documentaire : 7 tests sur 7 réussis ;
- build complet : 359 jobs réussis ;
- audit global : 32 593 constantes, 356 modules, 612 exceptions générées,
  aucune exception écrite ;
- échecs attendus : 57 fixtures rejetées aux diagnostics, lignes et colonnes
  exacts, sans erreur supplémentaire ;
- inventaire de non-perte : 397 attendus, 397 trouvés, aucun manquant, extra ou
  doublon, aucune garantie indispensable ouverte ;
- contrôle des passages et empreintes après enregistrement : 21 affirmations
  et 138 références cohérentes ;
- compilation des références du registre : 110 déclarations publiques et
  28 déclarations de test résolues.

Après le commit du registre, `scripts/verify.ps1` a été relancé sur l'arbre
livré. Il a validé les contrôles ci-dessus ainsi que les frontières d'import,
la stratification de 304 modules de production et les gates de code généré ;
son verdict terminal couvre 357 fichiers Lean. Aucun push, merge ou audit
extérieur n'est conclu par le présent rapport.
