# Génération constitutive, occurrences et bornes locales

Ce passage poursuit la demande de fermer les calculs internes, calculer leurs
bornes et raccorder le secours au présent conservé et rechargé. Il part de
`eb989d51f0c91a2675c893400fa095b2331084df`, sur
`codex/align-persist-recovery`, et conserve la
[cible v0.3](RP_ALIGN_PERSIST_SPEC_v0_3.fr.md).
**Le raccord final du secours n'est pas encore implémenté.** La fermeture
transitive de D2 reste nécessaire avant les enveloppes globales de D3 et la
garantie de D4. Les égalités et bornes établies ici sont celles des composants
précisément désignés ci-dessous.

## Générer depuis la source effectivement reçue

[Le générateur contrôlé](../../Tests/LocalAlignment/DocumentaryControlConstitutiveGeneration.lean)
remplace l'appel atomique à `generateCanonicalStageFromSource` dans
[`ControlNextState.generationCode`](../../Tests/LocalAlignment/DocumentaryControlNextState.lean).
Il ouvre l'avancement du curseur, la lecture explicite, la compatibilité,
la remontée du code de différence jusqu'à son obstruction initiale et la
lecture de provenance. Ces productions constituent la couche libre.

La cible et les lois de génération consomment cette même couche. La cible
stocke la formation et son code de frontière. Les lois conservent la
compatibilité produite, l'intégration de provenance, la continuation et le
nouvel enregistrement de formation. Le paquet `CanonicalStageGeneration`
est construit à partir du couple cible/pas effectivement retourné. Ses quatre
compteurs sont ceux de l'original. L'égalité porte sur ce paquet entier.

Pour tout code de différence reçu, `obstruction_bounded` établit la borne
structurale `o`, avec `o = 1` au code initial et `o = o_précédent + 1` à chaque
formation. Pour toute source positive de la présentation exemple indexée
par un stade `depth`, `canonical_bounded` établit une borne de **`o + 31`
transitions étiquetées**. L'ouverture intérieure du générateur est générique
en la présentation circulaire ; le paquet `CanonicalStageGeneration` reste
celui de la présentation exemple employée par le maître.

## Calculer cette borne avant la génération

[Le bootstrap local](../../Tests/LocalAlignment/DocumentaryControlGenerationBudget.lean)
parcourt le code de différence reçu. Il retourne le compte réellement
calculé, puis l'addition contrôlée de 31 produit l'allocation pour le
générateur. Il n'exécute ni le générateur ni son évaluateur pour obtenir
cette allocation.

`obstruction_bound_bounded` borne ce parcours par `b`, défini par `b = 1`
au code initial et `b = b_précédent + 2` à chaque formation.
`canonical_bound_bounded` borne le calcul complet de l'allocation par
`b + 64` : 63 transitions pour l'addition contrôlée de 31 et une pour le
paquet retourné. `computed_allowance_ready` prouve que l'allocation
effectivement produite suffit au générateur contrôlé. Cette preuve ne
demande pas en hypothèse que ce générateur a déjà réussi.

Ce sont des bornes du modèle de transitions déclaré par `Control.Code`.
Elles ne ferment pas les coûts administratifs de tous ses `bind`, du runner,
de l'allocation physique ou des autres opérations du maître. Elles ne sont
donc pas l'enveloppe globale de D3.

## Constituer le rôle et ses occurrences sans régénérer leurs états

[La formation du rôle](../../Tests/LocalAlignment/DocumentaryControlRoleFormation.lean)
construit explicitement les fonctions de séparation et de réunion, puis le
paquet de rôle avec la relation exécutée et ses continuations réelles.
`role_bounded` donne cinq transitions pour cette formation. L'invocation
future du lecteur d'assignation contenu dans la fonction de séparation
reste une obligation distincte.

Le cache d'endpoints lit les champs source et cible du schedule déjà stocké
par le stade exécuté. Sa formation est payée par `endpointsCode`. Les
réalisations gauche et droite réemploient ces états, avec leurs témoins de
formation indexés. Elles ne rappellent pas le constructeur des enfants.
Les identités portent les témoins de source, formation, cible et provenance.
L'évidence de constitution relit les témoins de l'identité effectivement
produite ; la licence consomme les deux identités et leurs évidences.

Les majorants locaux sont trois transitions pour une réalisation, huit
pour une identité, une pour son évidence et dix-neuf pour la licence entière.
Ils conservent les paquets originaux et leurs distinctions d'occurrences.

## Consommer les endpoints stockés dans le transport et son lecteur

[Le raccord des indices](../../Tests/LocalAlignment/DocumentaryControlScheduleCache.lean)
aligne le programme et son entrée sur les endpoints du schedule conservé.
Le transport contrôlé reçoit ces endpoints. Le lecteur de l'assignation
suivante est également formé à partir de ce programme et de ces endpoints.
Les égalités changent les indices sans reconstruire un schedule.

L'égalité du stade séquentiel entier est conservée, ainsi que celle du
lecteur et de son travail pour toute requête. L'exécution intérieure de ces
requêtes différées n'est pas fermée par cette égalité. Le contrôle C rejette
désormais tout appel à `DiscoverySchedule.entry` dans la portée étendue.

## Vérification et obligations restantes

[Les preuves de cas](../../Tests/LocalAlignment/DocumentaryGenerationBudgetCases.lean)
établissent, pour tout `depth`, que le bootstrap fournit une allocation
utilisable pour le même générateur. Elles conservent aussi l'égalité du
paquet entier, la stabilité avec du combustible supplémentaire et le rejet
en dessous de la longueur de la trace exécutée.

Le [protocole de développement](../../scripts/run-documentary-generation-budget-smoke.py)
teste quatre histoires, aux profondeurs 0, 1, 2 et 5. Il exécute d'abord le
bootstrap, utilise sa sortie pour le générateur, puis vérifie les comptes,
le combustible exact, une unité insuffisante et le surplus. Ses quatre
audits runtime sont sans axiome. Le plafond de bootstrap vient de la borne
du composant, pas d'un essai réussi de génération.

Le protocole d'intégration précédent conserve ses 31 cas et ses critères
de sortie. Ses attentes de paquets de ressources passent de 9 à 11 pour
une citation et de 7 à 9 pour un refus : le nouveau générateur et le cache
d'endpoints ajoutent chacun une formation payée. Les anciens relevés et
leurs empreintes restent historiques.

La gate complète a réussi sur 342 fichiers Lean : 27 554 constantes auditées,
aucune exception pour une déclaration écrite, 552 audits explicites des
43 modules de contrôle sans axiome et 23 échecs attendus avec leurs diagnostics
exacts. Les 31 contrôles d'intégration et leurs seize audits runtime passent,
ainsi que les quatre histoires du bootstrap et leurs quatre audits runtime.
Les gardes C rejettent 842 mutations textuelles. Elles comptent douze sites
natifs de lectures des métadonnées de tête et zéro appel de reconstruction
d'endpoints de schedule dans leur portée.

La [qualification de cet arbre](controle-generation-roles-bornes-verification.json)
consigne les empreintes et la portée ; la
[qualification précédente](controle-tete-assemblages-verification.json)
n'est pas réécrite.

| Obligation de la chaîne demandée | État après ces constructions |
| --- | --- |
| Générateur constitutif et partage de sa couche | Décomposés dans le contrôle, accord du paquet entier et borne locale prouvés |
| Formation du rôle, des occurrences et de leurs évidences | Raccordée aux endpoints déjà produits ; appels futurs de fonctions encore à instrumenter |
| Reconstructions d'endpoints de schedule | Les deux sites restants sont remplacés par les endpoints stockés |
| Métadonnées dépendantes de tête | Douze sites natifs de lectures restent ouverts ; les autres indices exécutables doivent aussi être examinés |
| Ouverture documentaire, normalisation, préservation et routage | Calculs internes encore à ouvrir |
| Lecteurs d'assignation, frames et codecs | Recettes à raccorder à toute la voie exécutée et portable |
| Administration, traces et allocations | Migration complète et enveloppes à établir |
| D3 : enveloppes obligatoires et successorales | Pas d'enveloppe globale fermée |
| D4 : secours sur le présent conservé et rechargé | `RecoveryData.prepare` appelle encore `Memory.step` nativement ; raccord borné restant |

La prochaine fermeture porte sur les métadonnées dépendantes, puis les
autres moteurs et lecteurs encore ouverts. Le présent mémorisé et ses
lois de rechargement existent déjà ; les invoquer ne fournit pas la borne
de l'exécution qui manque. D2, D3 et D4 restent ouverts, et A précède B.
